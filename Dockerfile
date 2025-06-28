FROM "coqorg/coq:8.19.2-ocaml-4.14.2-flambda"

ARG NJOBS=4

WORKDIR /home/coq/auth

COPY --chown=coq:coq auth.tar.gz .
RUN tar -xvf auth.tar.gz

RUN set -x \
    && opam update -y \
    && opam pin add -n -y -k path auth . \
    && opam reinstall --forget-pending --yes \
    && opam install --confirm-level=unsafe-yes -j ${NJOBS} . --deps-only \
    && sudo chown -R coq:coq /home/coq/auth \
    && opam clean -a -c -s --logs \
    && make -j ${NJOBS}
