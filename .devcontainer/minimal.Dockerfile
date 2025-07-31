FROM ubuntu:24.04

SHELL ["/bin/bash", "-c"]

# Base dependencies: opam
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      libgmp-dev \
      opam \
      pkg-config \
    && apt-get clean -y
# FIXME: libgmp-dev and pkg-config should be installed automatically by opam,
# but it is not working, so just adding it above.

# Create a new user and give them sudo rights
ARG USER=vscode
RUN useradd -d /home/$USER -s /bin/bash -m $USER
RUN echo "$USER ALL=NOPASSWD: ALL" >> /etc/sudoers
USER $USER
ENV HOME /home/$USER
WORKDIR $HOME
RUN mkdir -p $HOME/bin

# Make sure ~/bin is in the PATH
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install OCaml
ARG OCAML_VERSION=4.12.1
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1
RUN opam install --yes batteries zarith stdint yojson dune menhir menhirLib pprint sedlex ppxlib process ppx_deriving ppx_deriving_yojson memtrace

# Get F* master and build
RUN eval $(opam env) \
 && source $HOME/.profile \
 && git clone https://github.com/FStarLang/FStar \
 && cd FStar/ \
 && git checkout v2025.08.07 \
 && opam install .

# Get compiled Z3
RUN sudo ./FStar/.scripts/get_fstar_z3.sh /usr/local/bin

# Instrument .profile and .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments fter the fact. Calling opam env here
# would perhaps thrash some variables set by the devcontainer infra.
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.profile
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.bashrc

# Also just link F* into bin
RUN eval $(opam env --set-switch) && ln -s $(which fstar.exe) $HOME/bin/fstar.exe
