FROM rust:alpine
COPY . /rust_ast
WORKDIR /rust_ast
RUN apk add --no-cache musl-dev
RUN ["cargo", "build", "--release"]
ENTRYPOINT ["./target/release/rust_ast"]
