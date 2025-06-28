# Paper mapping

## Section 2.1

- **Figure 1a**: [auth.ml](src/basic/auth.ml)  
  Note that we abbreviate `authenticated_computation` as `m` and `evidence` as `evi` in the paper.
- **Figure 1b**: [authentikit.v](theories/examples/authentikit.v)  
  Note that the Rocq formalization uses de Brujin indicies to represent type variables.  
- **Figure 2**: [merkle.ml](src/basic/merkle.ml)  
- **Figure 3a**: [prover.ml](src/basic/prover.ml)  
  The corresponding (untyped) Rocq term is found in [authentikit_list.v](theories/examples/authentikit_list.v) as `p_Authentikit`. 
- **Figure 3b**: [ideal.ml](src/basic/ideal.ml)  
  The corresponding (untyped) Rocq term is found in [authentikit.v](theories/examples/authentikit.v) as  `i_Authentikit`. 
- **Figure 3c**: [verifier.ml](src/basic/verifier.ml)  
  The corresponding (untyped) Rocq term is found in [authentikit_list.v](theories/examples/authentikit_list.v) as `v_Authentikit`. 
  
## Section 2.2/Figure 5

- **Untyped language**: [theories/heap_lang/lang.v](theories/heap_lang/lang.v)  
  Note that term-level type operators, e.g. $\Lambda e$, is defined as notation in [theories/typing/typing.v](theories/typing/typing.v)
- **Syntactic types**: [theories/typing/types.v](theories/typing/types.v). 
- **Syntactic typing judgment**: [theories/typing/typing.v](theories/typing/typing.v).  
  The typing judgment $\Theta | \Gamma \vdash e~:~\tau$ is written `Θ |ₜ Γ ⊢ₜ e : τ` in the Rocq formalization.
   
## Section 3

CF-SL is derived using a generic "up-to-bad logic" defined in [program_logic_upto_bad/](theories/program_logic_upto_bad/). To obtain CF-SL, we specialize the generic logic with the bad event being hash collision.

| Item             | File                                                                      | Name                   |
|------------------|---------------------------------------------------------------------------|------------------------|
| wp               | [weakestpre.v](theories/program_logic_upto_bad/weakestpre.v)              | `wp_def`, `wp_pre`     |
| $\mathcal{H}$    | [hash.v](theories/prelude/hash.v)                                         | `hash`                 |
| $\to$            | [lang.v](theories/heap_lang/lang.v)                                       | `base_step`, `HashS`   |
| $\to_{cf}$       | [weakestpre.v](theories/program_logic_upto_bad/weakestpre.v)              | `prim_step_not_bad`    |
| collisionFree    | [primitive_laws_upto_bad.v](theories/heap_lang/primitive_laws_upto_bad.v) | `hash_collision`       |
| collision        | [hash.v](theories/prelude/hash.v)                                         | `collision`            |
| Theorem 3.1      | [adequacy_upto_bad.v](theories/heap_lang/adequacy_upto_bad.v)             | `heap_adequacy_strong` |
| Fig. 6, wp-pure  | [lifting.v](theories/program_logic_upto_bad/lifting.v)                    | `wp_pure_step_later`   |
| Fig. 6, wp-alloc | [primitive_laws_upto_bad.v](theories/heap_lang/primitive_laws_upto_bad.v) | `wp_alloc`             |
| Fig. 6, wp-load  | [primitive_laws_upto_bad.v](theories/heap_lang/primitive_laws_upto_bad.v) | `wp_load`              |
| Fig. 6, wp-store | [primitive_laws_upto_bad.v](theories/heap_lang/primitive_laws_upto_bad.v) | `wp_store`             |
| Fig. 6, wp-val   | [weakestpre.v](theories/program_logic_upto_bad/weakestpre.v)              | `wp_value`             |
| Fig. 6, wp-bind  | [weakestpre.v](theories/program_logic_upto_bad/weakestpre.v)              | `wp_bind`              |
| Fig. 6, wp-wand  | [weakestpre.v](theories/program_logic_upto_bad/weakestpre.v)              | `wp_wand_l`            |
| hashed           | [hashes_auth.v](theories/base_logic/hashes_auth.v)                        | `hashed`               |
| wp-hash          | [primitive_laws_upto_bad.v](theories/heap_lang/primitive_laws_upto_bad.v) | `wp_hash`              |
| hash-validity    | [hashes_auth.v](theories/base_logic/hashes_auth.v)                        | `hashed_inj_or_coll`   |
| Corollary 3.2    | [adequacy.v](theories/rel_logic_bin/adequacy.v)                           | `refines_adequacy`     |

The $spec$ resource is defined using the resource algebra defined in [spec_ra.v](theories/base_logic/spec_ra.v). In the binary CFSL logic, `spec` is defined as `spec_ideal` found in [model.v](theories/rel_logic_bin/model.v) and governed by the rules found in [model.v](theories/rel_logic_bin/spec_rules.v), e.g., `step_ideal_load`.

`REL eᵥ << eᵢ : A` is notation for `refines` as found in [model.v](theories/rel_logic_bin/model.v) used to state Corollary 3.2.

## Section 4, 4.1

The logical relation $\Theta | \Gamma ⊨ e_1 \preceq e_2 ~ : ~\tau$ is written `{Θ;Δ;Γ} ⊨ e1 ≤log≤ e2 : τ` in the Rocq formalization.

| Item                   | File                                                                         | Name                                           |
|------------------------|------------------------------------------------------------------------------|------------------------------------------------|
| Theorem 4.1            | [authentikit_list_security.v](theories/examples/authentikit_list_security.v) | `authentikit_security_syntactic`               |
| kind interpretation    | [interp.v](theories/rel_logic_bin/interp.v)                                  | `kindO`                                        |
| type interpretation    | [interp.v](theories/rel_logic_bin/interp.v)                                  | `interp_def`, `⟦ τ ⟧`                          |
| context interpretation | [interp.v](theories/rel_logic_bin/interp.v)                                  | `env_ltyped`, `⟦ Γ ⟧*`                         |
| term interpretation    | [model.v](theories/rel_logic_bin/model.v)                                    | `refines`                                      |
| logical relation       | [interp.v](theories/rel_logic_bin/interp.v)                                  | `bin_log_related`, `{Θ;Δ;Γ} ⊨ e1 ≤log≤ e2 : τ` |
| compatibility lemmas   | [fundamental.v](theories/rel_logic_bin/fundamental.v)                        | e.g. `bin_log_related_app`                     |
| Theorem 4.2            | [fundamental.v](theories/rel_logic_bin/fundamental.v)                        | `fundamental`                                  |

## Section 4.2

The proof is found in [authentikit_base_security.v](theories/examples/authentikit_base_security.v) and [authentikit_list_security.v](theories/examples/authentikit_list_security.v). See in particular:

- `refines_authentikit`, `lrel_auth_comp`, `refines_auth_unauth` in [authentikit_list_security.v](theories/examples/authentikit_list_security.v)
- `lrel_auth` in [authentikit_base_security.v](theories/examples/authentikit_base_security.v)
- **Lemma 4.3**: `authentikit_security` in [authentikit_list_security.v](theories/examples/authentikit_list_security.v)

## Section 5, 5.1

The logical relation $\Theta | \Gamma ⊨ e_1 \preceq e_2 \preceq e_3 ~ : ~\tau$ is written `{Θ;Δ;Γ} ⊨ e1 ≤log≤ e2 ≤log≤ e3 : τ` in the Rocq formalization.

| Item                   | File                                                                               | Name                                                    |
|------------------------|------------------------------------------------------------------------------------|---------------------------------------------------------|
| Theorem 5.1            | [authentikit_list_correctness.v](theories/examples/authentikit_list_correctness.v) | `authentikit_correctness_syntactic`                     |
| kind interpretation    | [interp.v](theories/rel_logic_tern/interp.v)                                       | `kindO`                                                 |
| type interpretation    | [interp.v](theories/rel_logic_tern/interp.v)                                       | `interp_def`, `⟦ τ ⟧`                                   |
| context interpretation | [interp.v](theories/rel_logic_tern/interp.v)                                       | `env_ltyped`, `⟦ Γ ⟧*`                                  |
| term interpretation    | [model.v](theories/rel_logic_tern/model.v)                                         | `refines`                                               |
| logical relation       | [interp.v](theories/rel_logic_tern/interp.v)                                       | `bin_log_related`, `{Θ;Δ;Γ} ⊨ e1 ≤log≤ e2 ≤log≤ e3 : τ` |
| compatibility lemmas   | [fundamental.v](theories/rel_logic_tern/fundamental.v)                             | e.g. `bin_log_related_app`                              |
| Theorem 5.2            | [fundamental.v](theories/rel_logic_tern/fundamental.v)                             | `fundamental`                                           |

## Section 5.2

The proof is found in [authentikit_base_correctness.v](theories/examples/authentikit_base_correctness.v) and [authentikit_list_correctness.v](theories/examples/authentikit_list_correctness.v). See in particular:

- `refines_authentikit`, `lrel_auth_comp`, `refines_auth_unauth` in [authentikit_list_correctness.v](theories/examples/authentikit_list_correctness.v)
- `p_unauth` in [authentikit_list.v](theories/examples/authentikit_list.v)
- `wp_resolve_proph_string` , `lrel_auth` in [authentikit_base_correctness.v](theories/examples/authentikit_base_correctness.v)
- **Lemma 5.3**: `authentikit_correctness` in [authentikit_list_correctness.v](theories/examples/authentikit_list_correctness.v)

## Section 6

### Proof accumulator

- **Implementation**: [authentikit_rev_list.v](theories/examples/authentikit_rev_list.v)
- **Correctness**: [authentikit_rev_list_correctness.v](theories/examples/authentikit_rev_list_correctness.v)

### Reuse Buffering

- **Implementation**: [authentikit_buf.v](theories/examples/authentikit_buf.v)
- **Security**: [authentikit_buf_security.v](theories/examples/authentikit_buf_security.v)
- **Correctness**: [authentikit_buf_correctness.v](theories/examples/authentikit_buf_correctness.v)

### Heterogeneous Reuse Buffering

- **Implementation**: [authentikit_buf_magic.v](theories/examples/authentikit_buf_magic.v)
- **Security**: [authentikit_buf_magic_security.v](theories/examples/authentikit_buf_magic_security.v)
- **Correctness**: [authentikit_buf_magic_correctness.v](theories/examples/authentikit_buf_magic_correctness.v)

### Stateful Buffering

- **Implementation**: [authentikit_buf_magic_state.v](theories/examples/authentikit_buf_magic_state.v)
- **Security**: [authentikit_buf_magic_state_security.v](theories/examples/authentikit_buf_magic_state_security.v)
- **Correctness**: [authentikit_buf_magic_state_correctness.v](theories/examples/authentikit_buf_magic_state_correctness.v)

## Section 7

- **Implementation**: [merkle.v](theories/examples/merkle.v), see `t_retrieve`, `p_retrieve`, and `v_retrieve`
- **Security**:[merkle_retrieve_security.v](theories/examples/merkle_retrieve_security.v), see `refines_retrieve`
- **Correctness**: [merkle_retrieve_correctness.v](theories/examples/merkle_retrieve_correctness.v), see `refines_retrieve`.
- **Semantically-typed Merkle Module**: [merkle_syntactic.v](theories/examples/merkle_syntactic.v), see `refines_merkle_module_security` and `refines_merkle_module_correctness`.
