COMPILER=ocamlfind ocamlopt 
COMPILER_OPT=ocamlfind ocamlopt -w -55 -w -53

noinline:
	$(COMPILER_OPT) -c utils.ml
	$(COMPILER_OPT) -c -package sha hash.ml
	$(COMPILER_OPT) -c authenticatable_base.ml
	$(COMPILER_OPT) -c auth.ml
	$(COMPILER_OPT) -c merkle.ml
	$(COMPILER_OPT) -c redblack.ml
	$(COMPILER_OPT) -c prover_rev.ml
	$(COMPILER_OPT) -c prover_buf.ml
	$(COMPILER_OPT) -c prover.ml
	$(COMPILER_OPT) -c prover_buf_magic_state.ml
	$(COMPILER_OPT) -c verifier.ml
	$(COMPILER_OPT) -c verifier_buf.ml
	$(COMPILER_OPT) -c verifier_buf_magic.ml
	$(COMPILER_OPT) -c verifier_buf_magic_state.ml
	$(COMPILER_OPT) -c ideal.ml
	$(COMPILER_OPT) -c -package batteries test_utils.ml
	$(COMPILER_OPT) -thread -linkpkg -package batteries,sha utils.cmx hash.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_rev.cmx prover_buf.cmx prover.cmx prover_buf_magic_state.cmx verifier.cmx verifier_buf.cmx verifier_buf_magic.cmx verifier_buf_magic_state.cmx ideal.cmx test_utils.cmx -o test test.ml
