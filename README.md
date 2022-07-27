# lin_inf crate

## Running
This repository provides the `lin_inf` crate as a rust library. It also provides an executable to search through linear inferences which uses this library.

The executable can be run with:
```
cargo run --release
```
which provides the user with a help interface. Note that the `--release` flag builds the program with optimisations and is crucial for good performance.

### Examples

Search 7-variable inferences for those that cannot be derived from switch and medial:
```
cargo run --release search --p4 -s -m
```

Generate the basis of 6 variable graph rewrites, and print no cache files:
```
cargo run --release basis 6 --no-write
```

## Documentation
Full documentation for the library can be found [here](https://alexarice.github.io/lin_inf/lin_inf/index.html) (best viewed by downloading the repository and opening the file in a browser).
