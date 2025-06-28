COMPILER=ocamlfind ocamlopt 
COMPILER_ALL=ocamlfind ocamlopt -w -55 -w -53

all:
	$(COMPILER_ALL) -c utils.ml
#       $(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha1_stubs.c sha1.mli sha1.ml
#       $(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha256_stubs.c sha256.mli sha256.ml
	$(COMPILER_ALL) -c -package sha proof.ml
	$(COMPILER_ALL) -c authenticatable_base.ml
	$(COMPILER_ALL) -c authenticatable_marshal.ml
	$(COMPILER_ALL) -c auth.ml
	$(COMPILER_ALL) -c merkle.ml
	# $(COMPILER) -c trimerkle.ml
	$(COMPILER_ALL) -c redblack.ml
	# $(COMPILER) -c merkle_sparse.ml
	$(COMPILER_ALL) -c prover.ml
	$(COMPILER_ALL) -c prover_marshal.ml
	$(COMPILER_ALL) -c prover_io.ml
	$(COMPILER_ALL) -c prover_io_batch.ml
	$(COMPILER_ALL) -c prover_susp.ml
#       $(COMPILER) -c prover_buf.ml
#	$(COMPILER) -c prover_orig.ml
#       $(COMPILER) -c prover_buf_magic_state.ml
	$(COMPILER_ALL) -c verifier.ml
	$(COMPILER_ALL) -c verifier_marshal.ml
	$(COMPILER_ALL) -c verifier_io.ml
	$(COMPILER_ALL) -c verifier_io_batch.ml
	$(COMPILER_ALL) -c verifier_susp.ml
#       $(COMPILER) -c verifier_buf.ml
#       $(COMPILER) -c verifier_buf_magic.ml
#       $(COMPILER) -c verifier_buf_magic_state.ml
	$(COMPILER_ALL) -c ideal.ml
	$(COMPILER_ALL) -c -package batteries test_utils.ml
	$(COMPILER_ALL) -thread -linkpkg -package batteries,sha utils.cmx proof.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover.cmx prover_susp.cmx prover_io.cmx prover_io_batch.cmx prover_marshal.cmx verifier.cmx verifier_susp.cmx verifier_marshal.cmx verifier_io.cmx verifier_io_batch.cmx ideal.cmx test_utils.cmx -o test test.ml
        # $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authent>
        # $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authent>
	$(COMPILER_ALL) -thread -linkpkg -package batteries,sha utils.cmx proof.cmx authenticatable_marshal.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover.cmx prover_susp.cmx prover_io.cmx prover_io_batch.cmx prover_marshal.cmx verifier.cmx verifier_susp.cmx verifier_marshal.cmx verifier_io.cmx verifier_io_batch.cmx ideal.cmx test_utils.cmx -o bench bench.ml

noinline:
	$(COMPILER) -c utils.ml
#       $(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha1_stubs.c sha1.mli sha1.ml
#       $(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha256_stubs.c sha256.mli sha256.ml
	$(COMPILER) -c -package sha proof.ml
	$(COMPILER) -c authenticatable_base.ml
	$(COMPILER) -c authenticatable_marshal_401.ml
	$(COMPILER) -c auth.ml
	$(COMPILER) -c merkle.ml
	# $(COMPILER) -c trimerkle.ml
	$(COMPILER) -c redblack.ml
	# $(COMPILER) -c merkle_sparse.ml
	$(COMPILER) -c prover_401.ml
	$(COMPILER) -c prover_marshal_401.ml
	$(COMPILER) -c prover_io_401.ml
#       $(COMPILER) -c prover_buf.ml
#	$(COMPILER) -c prover_orig.ml
#       $(COMPILER) -c prover_buf_magic_state.ml
	$(COMPILER) -c verifier_401.ml
	$(COMPILER) -c verifier_marshal_401.ml
	$(COMPILER) -c verifier_io_ni.ml
#       $(COMPILER) -c verifier_buf.ml
#       $(COMPILER) -c verifier_buf_magic.ml
#       $(COMPILER) -c verifier_buf_magic_state.ml
	$(COMPILER) -c ideal_401.ml
	$(COMPILER) -c -package batteries test_utils_ni.ml
        # $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authent>
        # $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authent>
        # $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authent>
	$(COMPILER) -thread -linkpkg -package batteries,sha utils.cmx proof.cmx authenticatable_marshal_401.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_401.cmx prover_io_401.cmx prover_marshal_401.cmx verifier_401.cmx verifier_marshal_401.cmx verifier_io_ni.cmx ideal_401.cmx test_utils_ni.cmx -o bench_ni bench_ni.ml

fourone:
	$(COMPILER) -c utils.ml
#	$(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha1_stubs.c sha1.mli sha1.ml
#	$(COMPILER) -c -ccopt -Wall -ccopt -O3 -ccopt -funroll-loops sha256_stubs.c sha256.mli sha256.ml
	$(COMPILER) -c -package sha proof.ml
	$(COMPILER) -c authenticatable_base.ml
	$(COMPILER) -c authenticatable_marshal_401.ml
	$(COMPILER) -c auth.ml
	$(COMPILER) -c merkle.ml
	# $(COMPILER) -c trimerkle.ml
	$(COMPILER) -c redblack.ml
	# $(COMPILER) -c merkle_sparse.ml
	$(COMPILER) -c prover_401.ml
	$(COMPILER) -c prover_marshal_401.ml
	$(COMPILER) -c prover_io_401.ml
#	$(COMPILER) -c prover_buf.ml
#	$(COMPILER) -c prover_orig.ml
#	$(COMPILER) -c prover_buf_magic_state.ml
	$(COMPILER) -c verifier_401.ml
	$(COMPILER) -c verifier_marshal_401.ml
	$(COMPILER) -c verifier_io_401.ml
#	$(COMPILER) -c verifier_buf.ml
#	$(COMPILER) -c verifier_buf_magic.ml
#	$(COMPILER) -c verifier_buf_magic_state.ml
	$(COMPILER) -c ideal_401.ml
	$(COMPILER) -c -package batteries test_utils_401.ml
	# $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authenticatable_base.cmx merkle.cmx trimerkle.cmx redblack.cmx prover.cmx prover_buf.cmx prover_orig.cmx prover_buf_magic_state.cmx verifier.cmx verifier_buf.cmx verifier_buf_magic.cmx verifier_buf_magic_state.cmx ideal.cmx test_utils.cmx -o test_tri test_tri.ml
	# $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authenticatable_base.cmx merkle.cmx trimerkle.cmx redblack.cmx prover.cmx prover_buf.cmx prover_orig.cmx prover_buf_magic_state.cmx verifier.cmx verifier_buf.cmx verifier_buf_magic.cmx verifier_buf_magic_state.cmx ideal.cmx test_utils.cmx -o test test.ml
	# $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench utils.cmx proof.cmx auth.cmx authenticatable_base.cmx merkle.cmx trimerkle.cmx redblack.cmx prover.cmx prover_buf.cmx prover_orig.cmx prover_buf_magic_state.cmx verifier.cmx verifier_buf.cmx verifier_buf_magic.cmx verifier_buf_magic_state.cmx ideal.cmx test_utils.cmx -o test_rb test_rb.ml
	$(COMPILER) -thread -linkpkg -package batteries,sha utils.cmx proof.cmx authenticatable_marshal_401.cmx auth.cmx authenticatable_base.cmx merkle.cmx redblack.cmx prover_401.cmx prover_io_401.cmx prover_marshal_401.cmx verifier_401.cmx verifier_marshal_401.cmx verifier_io_401.cmx ideal_401.cmx test_utils_401.cmx -o bench_401 bench_401.ml
	# $(COMPILER) -thread -linkpkg -package core -package core_unix.command_unix -package core_bench auth.cmx authenticatable_base.cmx merkle.cmx proof.cmx prover.cmx prover_buf.cmx verifier.cmx verifier_buf.cmx ideal.cmx test_utils.cmx -o test_sparse test_sparse.ml
