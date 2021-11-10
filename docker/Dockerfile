FROM ocaml/opam:debian-10-ocaml-4.11

RUN sudo apt-get update &&\
    sudo apt-get install -y cvc4 z3

RUN opam update &&\
    opam depext -i\
    dune.2.9.1 dune-site menhir zarith ppx_deriving_yojson ocamlgraph alt-ergo frama-c re
ENV PATH=$PATH:/home/opam/.opam/4.11/bin

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH=$PATH:/home/opam/.cargo/bin
RUN cargo install tokei

RUN why3 config detect

COPY init.sh $HOME/

CMD ["/bin/bash", "--init-file", "~/init.sh"]
