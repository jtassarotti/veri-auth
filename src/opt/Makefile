COMPILER=ocamlfind ocamlopt 
COMPILER_OPT=ocamlfind ocamlopt -w -55 -w -53 -w -10

opt:
	$(COMPILER_OPT) -c -package batteries utils.ml
	$(COMPILER_OPT) -c -package sha hash.ml
	$(COMPILER_OPT) -c authenticatable_base.ml
	$(COMPILER_OPT) -c authenticatable_marshal.ml
	$(COMPILER_OPT) -c auth.ml
	$(COMPILER_OPT) -c merkle.ml
	$(COMPILER_OPT) -c redblack.ml
	$(COMPILER_OPT) -c prover_rev.ml
	$(COMPILER_OPT) -c prover_marshal.ml
	$(COMPILER_OPT) -c prover_io.ml
	$(COMPILER_OPT) -c verifier.ml
	$(COMPILER_OPT) -c verifier_marshal.ml
	$(COMPILER_OPT) -c verifier_io.ml
	$(COMPILER_OPT) -c ideal.ml
	$(COMPILER_OPT) -c -package batteries test_utils.ml
	$(COMPILER_OPT) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_io.cmx prover_marshal.cmx verifier.cmx verifier_marshal.cmx verifier_io.cmx ideal.cmx test_utils.cmx -o test test.ml
	$(COMPILER_OPT) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_io.cmx prover_marshal.cmx verifier.cmx verifier_marshal.cmx verifier_io.cmx ideal.cmx test_utils.cmx -o bench_rb bench_rb.ml
	$(COMPILER_OPT) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_io.cmx prover_marshal.cmx verifier.cmx verifier_marshal.cmx verifier_io.cmx ideal.cmx test_utils.cmx -o bench_mtree bench_mtree.ml
