# private-games on LeanAPI. Build context: the leanapi checkout.
#   docker build -f examples/private-games/Dockerfile -t private-games .
# leancrypto is private: pass a token with read access, e.g.
#   docker build --secret id=gh,env=GH_TOKEN ...
FROM debian:bookworm-slim AS build

RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl git pkg-config libssl-dev \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/usr/local/elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none \
    && elan toolchain install leanprover/lean4:v4.33.0 \
    && elan default leanprover/lean4:v4.33.0

WORKDIR /src/leanapi
COPY . /src/leanapi
RUN --mount=type=secret,id=gh \
    if [ -f /run/secrets/gh ]; then \
      git config --global url."https://x-access-token:$(cat /run/secrets/gh)@github.com/".insteadOf "https://github.com/"; \
    fi \
    && rm -rf .lake && lake build games

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates libgmp10 libstdc++6 \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/leanapi/.lake/build/bin/games /usr/local/bin/games
ENV PORT=8080
EXPOSE 8080
VOLUME /data
CMD ["sh", "-c", "exec games --host 0.0.0.0 --port ${PORT:-8080} --db ${DB_PATH:-/data/games.sqlite}"]
