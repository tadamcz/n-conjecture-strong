FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git build-essential zstd python3 python3-sympy \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:${PATH}
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.27.0 \
    && rm /tmp/elan-init.sh

WORKDIR /opt/strong-four
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN lake exe cache get
COPY StrongFour/ StrongFour/
COPY StrongFour.lean Audit.lean ./
COPY scripts/check.sh scripts/check_construction.py scripts/
RUN bash scripts/check.sh

CMD ["bash"]
