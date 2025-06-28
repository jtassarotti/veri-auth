COMPILER=ocamlfind ocamlopt 
COMPILER_ALL=ocamlfind ocamlopt -w -55 -w -53

all:
	$(COMPILER) -c -package batteries utils.ml
	$(COMPILER) -c -package sha hash.ml
	$(COMPILER) -c authenticatable_base.ml
	$(COMPILER) -c authenticatable_marshal.ml
	$(COMPILER) -c auth.ml
	$(COMPILER) -c merkle.ml
	$(COMPILER) -c redblack.ml
	$(COMPILER) -c prover_rev.ml
	$(COMPILER) -c prover_marshal.ml
	$(COMPILER) -c prover_io.ml
	$(COMPILER) -c verifier.ml
	$(COMPILER) -c verifier_marshal.ml
	$(COMPILER) -c verifier_io.ml
	$(COMPILER) -c ideal.ml
	$(COMPILER) -c test_utils.ml
	$(COMPILER) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_io.cmx prover_marshal.cmx verifier.cmx verifier_marshal.cmx verifier_io.cmx ideal.cmx test_utils.cmx -o bench_rb bench_rb.ml
	$(COMPILER) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_io.cmx prover_marshal.cmx verifier.cmx verifier_marshal.cmx verifier_io.cmx ideal.cmx test_utils.cmx -o bench_mtree bench_mtree.ml