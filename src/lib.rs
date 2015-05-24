//! Implementation of JSON-RPC specification.
//!
//! This package provides a basic implementation for [JSON-RPC
//! Specification](http://www.jsonrpc.org/specification). All
//! parameters are required to implement the `Encodable` trait and all
//! result types are required to implement the `Decodable` trait.
//!
//! Implemented functionality:
//!
//! - Ability to make JSON-RPC calls
//!
//! TODO:
//!
//! - Send notifications (calls without an ID)
//! - Batch requests

extern crate rustc_serialize;
extern crate hyper;
extern crate url;
extern crate uuid;

use rustc_serialize::{Encoder, Encodable, Decoder, Decodable};

// These constants are defined by the JSON-RPC standard
const PARSE_ERROR: i64 = -32700; // Invalid JSON was received by the server.
const INVALID_REQUEST: i64 = -32600; // The JSON sent is not a valid Request object.
const METHOD_NOT_FOUND: i64 = -32601; // The method does not exist / is not available.
const INVALID_PARAMS: i64 = -32602; // Invalid method parameter(s).
const INTERNAL_ERROR: i64 = -32603; // Internal JSON-RPC error.
// -32000 to -32099 	// Server error Reserved for implementation-defined server-errors.

/// This enum represents error codes of the protocol as they are
/// [defined by the
/// specification](http://www.jsonrpc.org/specification#error_object).
#[cfg_attr(test, derive(Debug))]
pub enum ErrorCode {
    ParseError,
    InvalidRequest,
    MethodNotFound,
    InvalidParams,
    InternalError,
    ServerError(i64)
}

impl ErrorCode {
    fn from(err_code: i64) -> ErrorCode {
        match err_code {
            PARSE_ERROR => ErrorCode::ParseError,
            INVALID_REQUEST => ErrorCode::InvalidRequest,
            METHOD_NOT_FOUND => ErrorCode::MethodNotFound,
            INVALID_PARAMS => ErrorCode::InvalidParams,
            INTERNAL_ERROR => ErrorCode::InternalError,
            _ => ErrorCode::ServerError(err_code)
        }
    }

    fn to_error_code(&self) -> i64 {
        match *self {
            ErrorCode::ParseError => PARSE_ERROR,
            ErrorCode::InvalidRequest => INVALID_REQUEST,
            ErrorCode::MethodNotFound => METHOD_NOT_FOUND,
            ErrorCode::InvalidParams => INVALID_PARAMS,
            ErrorCode::InternalError => INTERNAL_ERROR,
            ErrorCode::ServerError(err_code) => err_code
        }
    }
}

impl Encodable for ErrorCode {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        try!(s.emit_i64(self.to_error_code()));
        Result::Ok(())
    }
}

impl Decodable for ErrorCode {
    fn decode<D: Decoder>(d: &mut D) -> Result<Self, D::Error>{
        d.read_i64().map(|v| ErrorCode::from(v))
    }
}

/// A struct that represents the actual error message sent by the
/// server. It can contain arbitrary data.
#[cfg_attr(test, derive(Debug))]
#[derive(RustcDecodable)]
pub struct Error<E> {
    pub code: ErrorCode,
    pub message: String,
    pub data: E
}

/// This enum encodes the response received from a JSON-RPC
/// server. Simply put, a response consists of a response or an
/// error and an ID.
#[cfg_attr(test, derive(Debug))]
pub enum Response<R,E>{
    Ok(R, String),
    Err(Error<E>, String)
}

impl <R: Decodable, E: Decodable> Decodable for Response<R,E> {
    fn decode<D: Decoder>(d: &mut D) -> Result<Self, D::Error>{
        let id: String = try!(d.read_struct_field("id", 0, |decoder| Decodable::decode(decoder)));
        let r: Result<R, D::Error> = d.read_struct_field("result", 0, |decoder| Decodable::decode(decoder));
        match r {
            Ok(v) => Ok(Response::Ok(v, id)),
            Err(_) => {
                let error: Error<E> = try!(d.read_struct_field("error", 0, |decoder| Decodable::decode(decoder)));
                Ok(Response::Err(error, id))
            }
        }
    }
}

impl <R,E> Response<R,E> {
    pub fn get_message_id(self) -> String {
        match self {
            Response::Ok(_, id) => id,
            Response::Err(_, id) => id
        }
    }
}

/// This module provides the main client functionality
pub mod client {

    use rustc_serialize::{Encodable, Decodable};
    use rustc_serialize::json::{self, DecoderError, EncoderError};
    use hyper;
    use std;
    use url;
    use std::io::Read;
    use uuid::Uuid;
    use super::{Response};

    /// This struct is the main error structure, used to encode
    /// different types of failures that might occur when running a
    /// JSON-RPC request.
    pub enum JsonRpcError{
        HttpError(hyper::error::Error),
        IOError(std::io::Error),
        JSONDecodingError(DecoderError),
        JSONEncodingError(EncoderError),
        URLError(url::ParseError)
    }

    pub type JsonRpcResult<R> = Result<R, JsonRpcError>;

    /// The request struct encodes a single RPC request. Parameter
    /// type `P` must implement the `Encodable` trait.
    #[derive(RustcDecodable, RustcEncodable)]
    struct Request<P> {
        jsonrpc: String,
        method: String,
        params: P,
        id: String
    }

    impl <P: Encodable> Request<P> {
        /// Build a new instance of a request.
        ///
        /// This method is the recommended way of building Request
        /// objects since it handles the generation of IDs per
        /// request.
        fn new (method_name: String, parameter: P) -> Request<P> {
            Request{ jsonrpc: "2.0".to_owned(),
                     method: method_name,
                     params: parameter,
                     id: Uuid::new_v4().to_string() }
        }
    }

    
    fn flat_map<T,K,F>(v: JsonRpcResult<T>, f: F) -> JsonRpcResult<K>
        where F: Fn(T) -> JsonRpcResult<K> {
        match v {
            Ok(o) => f(o),
            Err(e) => Err(e)
        }
    }

    /// A client is the main object that does the actual work of
    /// calling the JSON-RPC server and receiving the results.
    pub struct Client {
        endpoint: url::Url,
        http_client: hyper::client::Client
    }

    impl Client {
        /// Initialize a new client for a given HTTP endpoint using a
        /// default HTTP client
        pub fn new(endpoint: String) -> JsonRpcResult<Client> {
            let c = hyper::client::Client::new();
            Client::new_with_http_client(endpoint, c)
        }

        /// Initialize a new client for a given HTTP endpoint using
        /// the given HTTP client.
        ///
        /// This is especially useful when you want to fine tune your
        /// HTTP client (for example specific SSL rules etc...)
        ///
        /// # Failures
        ///
        /// It fails with a `URLError` if the given endpoint URL
        /// cannot be parsed by the `url` library.
        pub fn new_with_http_client(endpoint: String, c: hyper::client::Client) -> JsonRpcResult<Client> {
            match url::Url::parse(&endpoint) {
                Ok(url) => Ok(Client{endpoint: url, http_client: c}),
                Err(err) => Err(JsonRpcError::URLError(err))
            }
        }

        /// Call a JSON-RPC method with the given parameter.
        ///
        /// This method actually calls the endpoint for the given method and parameter.
        ///
        /// # Failures
        ///
        /// This method fails under following conditions:
        ///
        /// - The parameter cannot be encoded as JSON -> JSONEncodingError
        /// - The result type cannot be correctly decoded from JSON -> JSONDecodingError
        /// - Any problem with the HTTP communication -> HttpError
        /// - Any problem with network communication -> IOError
        pub fn call<P, R, E>(&mut self, method_name: String, parameter: P) -> JsonRpcResult<Response<R, E>>
            where P: Encodable, R: Decodable, E: Decodable {
                let request = Request::new(method_name, parameter);
                let encoded_request = json::encode(&request);
                match encoded_request {
                    Err(e) => Err(JsonRpcError::JSONEncodingError(e)),
                    Ok(v) => self.process_request(v)
                }
            }

        fn process_request<R, E>(&mut self, request: String) -> JsonRpcResult<Response<R, E>>
            where R: Decodable, E: Decodable {
                let bytes = request.as_bytes();
                let body = hyper::client::Body::BufBody(bytes, bytes.len());
                let result = self.http_client.post(self.endpoint.clone()).body(body).send();
                flat_map(result.map_err(|e|JsonRpcError::HttpError(e)), &Client::process_result)
            }

        fn process_result<R, E>(mut result: hyper::client::Response) -> JsonRpcResult<Response<R, E>>
            where R: Decodable, E: Decodable {
                let mut s: String = String::new();
                flat_map(result.read_to_string(&mut s).
                         map_err(JsonRpcError::IOError),
                         |_|json::decode(&s).
                         map_err(JsonRpcError::JSONDecodingError))
            }

    }
}

#[cfg(test)]
mod tests {

    use rustc_serialize::json;
    use std::collections::HashMap;
    use super::{ErrorCode, Response};

    #[derive(RustcDecodable, RustcEncodable, Debug)]
    struct TestParam {
        key: String,
        n: i64
    }

    /*
    #[test]
    fn test_request_encodes_to_json_correctly(){
        let req = Request::new("dont_panic".to_owned(), TestParam{key: "qwerty".to_owned(), n: 42});
        let encoded = json::encode(&req).unwrap();
        let expected = format!("{{\"jsonrpc\":\"2.0\",\"method\":\"dont_panic\",\"params\":{{\"key\":\"qwerty\",\"n\":42}},\"id\":\"{}\"}}", req.id);
        assert_eq!(expected, encoded);
    }
     */
    
    #[test]
    fn error_codes_encode_to_json_numbers() {
        let mut test_pairs = HashMap::new();
        test_pairs.insert(super::PARSE_ERROR, ErrorCode::ParseError);
        test_pairs.insert(super::INVALID_REQUEST, ErrorCode::InvalidRequest);
        test_pairs.insert(super::METHOD_NOT_FOUND, ErrorCode::MethodNotFound);
        test_pairs.insert(super::INVALID_PARAMS, ErrorCode::InvalidParams);
        test_pairs.insert(super::INTERNAL_ERROR, ErrorCode::InternalError);
        test_pairs.insert(42, ErrorCode::ServerError(42));
        for (k, v) in test_pairs.iter() {
            assert_eq!(format!("{}",k), json::encode(v).unwrap());
        }
    }

    #[test]
    fn test_normal_response_can_be_decoded(){
        let response = "{\"jsonrpc\":\"2.0\", \"result\":{\"key\":\"qwerty\",\"n\":42},\"id\":\"asdfg\"}";
        let response: Response<TestParam, String> = json::decode(&response).unwrap();
        let expected: Response<TestParam, String> = Response::Ok(TestParam{key: "qwerty".to_owned(), n: 42}, "asdfg".to_owned());
        assert_eq!(response.get_message_id(), expected.get_message_id());
    }

    #[test]
    fn test_error_response_can_be_decoded(){
        let response = "{\"jsonrpc\":\"2.0\", \"error\":{\"\":-32602,\"message\":\"Invalid API Key\",\"data\":{\"key\":\"qwerty\",\"n\":42}},\"id\":\"asdfg\"}";
        let response: Response<(), TestParam> = json::decode(&response).unwrap();
        let expected: Response<(), TestParam> = Response::Err(super::Error{code: ErrorCode::InvalidParams, message: "Invalid API Key".to_owned(), data: TestParam{key: "qwerty".to_owned(), n: 42}}, "asdfg".to_owned());
        assert_eq!(response.get_message_id(), expected.get_message_id());
    }
    
}
