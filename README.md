# whelk-rs

This is an experimental implementation of [Whelk](https://github.com/balhoff/whelk) in Rust

## Build

Clone this repo, change into the whelk-rs directory (```cd whelk-rs```), and then:
```shell
cargo build --release
```

## Running
```shell
./target/release/whelk -i uberon.owl
```

## Testing
```shell
cargo test --release -- --nocapture
```

## Profiling
The following instructions require installing [perf](https://perf.wiki.kernel.org/index.php/Main_Page) locally.  

For Ubuntu, one would do the following to install perf:
```shell
sudo apt-get install linux-tools-common linux-tools-generic linux-tools-`uname -r`
```

And then to run the profiler:
```shell
sudo perf record -g ./target/release/whelk -i <some_owl_file>
sudo perf script -F +pid > test.perf
```

Once the test.perf file is created, go to [Firefox Profiler](https://profiler.firefox.com) and click on the "Load a profile from file" button.  Use the generated test.perf file and enjoy! 
