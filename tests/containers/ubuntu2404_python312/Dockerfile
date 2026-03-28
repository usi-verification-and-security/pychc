# Use the official Ubuntu 24.04 base image
FROM ubuntu:24.04

# Set environment variables to prevent interactive prompts during build
ENV DEBIAN_FRONTEND=noninteractive
ENV PYTHONUNBUFFERED=1

# Install Python 3.12 and essential build tools
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3.12 \
    python3-venv \
    build-essential \
    curl \
    git \
    just \
    unzip \
    cmake \
    libgmp-dev \
    bison flex \
    openjdk-11-jre-headless \
    && curl https://sh.rustup.rs -sSf | sh -s -- -y \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* \
    && ln -sf /usr/bin/python3.12 /usr/bin/python3

ENV PATH="/root/.cargo/bin:${PATH}"

# Set the working directory
WORKDIR /app

COPY . .

# Default command
CMD ["/bin/bash", "-c", "just clean && just setup-test && just test"]
