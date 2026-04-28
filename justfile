set shell := ["fish", "-c"]

verified_crates := "abd abd-example echo echo-example echo-trivial specs verdist"
runnable_crates := "abd-example echo-example"

fmt:
    for crate in {{verified_crates}}; \
        pushd $crate; \
        verusfmt (fd '.rs'); \
        popd; \
    end

verify:
    for crate in {{verified_crates}}; \
        pushd $crate; \
        cargo verus verify; \
        popd; \
    end

check:
    for crate in {{verified_crates}}; \
        pushd $crate; \
        cargo check; \
        popd; \
    end

run:
    for crate in {{runnable_crates}}; \
        pushd $crate; \
        cargo run -- --no-delay; \
        popd; \
    end
