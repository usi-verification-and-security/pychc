FROM ubuntu:latest
ENV DEBIAN_FRONTEND=noninteractive

### System dependencies
RUN apt-get update && apt-get install -y \
    # basic python environment
    python3 python3-pip python3-venv \
    # for compiling opensmt and golem
    build-essential cmake make libgmp3-dev bison flex \
    # for getting github releases 
    git curl unzip tar bzip2 libssl-dev pkg-config \
    # for eldarica
    default-jre-headless \
    && rm -rf /var/lib/apt/lists/*

# Install Rust required by Carcara
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

# Create a Python virtual environment and make it the default python/pip
RUN python3 -m venv /venv
ENV PATH="/venv/bin:${PATH}"

#########################
# PyCHC installation
#########################

# Clone PyCHC from github
WORKDIR /root
RUN git clone https://github.com/usi-verification-and-security/pychc.git -b cav26ae

# Install Python requirements and the pySMT z3 backend (for QE)
WORKDIR /root/pychc
RUN pip install -r requirements.txt \
    && python -m pysmt install --z3 --confirm-agreement
RUN pip install -e .

# Install current solver releases and generate env.sh
RUN ./scripts/install_solvers.sh
# Install old solver releases used by the expected_bugs test suite
RUN ./scripts/install_solvers.sh pychc/tests/expected_bugs/old_binaries/ --old-releases

RUN cat env.sh >> ~/.bashrc

#########################
# Download benchmarks from CHC-COMP25
#########################

WORKDIR /root
RUN git clone https://github.com/chc-comp/chc-comp25-benchmarks.git

# Default working directory for interactive use
WORKDIR /root/pychc

CMD ["/bin/bash"]
