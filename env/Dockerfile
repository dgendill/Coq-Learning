FROM debian:8.2

RUN \
  apt-get update && \
  apt-get -y upgrade;

RUN apt-get --no-install-recommends -y install opam;
RUN apt-get -y install ocaml;
RUN apt-get -y install vim nano;

RUN opam init -y
RUN opam config setup -a
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update -y
RUN apt-get -y install build-essential
RUN opam install -y -j4 coq:flocq.2.4.0

# ADD go.sh /home/go.sh
# CMD ["/home/go.sh"]

# Define default command.
CMD ["bash"]

