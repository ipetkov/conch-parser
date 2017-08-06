#!/usr/bin/env bash

# Exit with an error if any command fails
set -e

# NB: cargo adds a unique identifier to all built tests/deps to disambiguate
# between different deps (e.g. libs, executables, integ tests, etc.), but this means
# that our deps directory could have other/older test files esp. if they were cached
# from a previous build.
#
# As of today there is no way to get cargo to clean up the test deps so we've got
# one of two options:
# 1) clean the entire directory and rebuild it - at the cost of extra build times
# 2) run cargo test, capture its output and infer which tests are actually relevant to run
#
# travis-cargo does both #1 and #2 above (but currently doesn't work with kcov so we're
# reimplementing its functionality here. #1 is largely due to recompiling with the
# link-dead-code flag, which we're already setting in the .travis.yml config, so it
# should be safe to skip doing #1
#
# Run cargo test here, due to previous compilations this should immediately run the
# tests (but no output will be shown, so if the tests take longer than 10mins to run
# it may be worth calling cargo through travis_wait).
#
# Then we extract any test files that get executed
for file in $(cargo test 2>&1 1>/dev/null | grep -oP '(?<=Running target\/debug\/).*'); do
	cov_dir="target/cov/$(basename "$file")";
	mkdir -p "$cov_dir"
	./kcov-build/usr/local/bin/kcov --exclude-pattern=/.cargo,/usr/lib --verify "$cov_dir" "target/debug/$file";
done

# Report the coverage to codecov
bash <(curl -s https://codecov.io/bash)
echo "Uploaded code coverage";
