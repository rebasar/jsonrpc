# JSON-RPC implementation for [Rust](http://www.rust-lang.org)

This is an implementation of JSON-RPC specification, entirely written in Rust.

The implementation is simple but currently lacks a lot of functionality.

## TODO:

- Implement batch calls
- Current implementation is bound to [hyper](https://crates.io/crates/hyper). Find a way to decouple it
so that alternative HTTP libraries can be used instead.
- Add examples.
- Add more tests (if anyone knows a public JSON-RPC service, please let me know)
