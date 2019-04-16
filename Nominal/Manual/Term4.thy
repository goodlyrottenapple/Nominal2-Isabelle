theory Term4
imports "../NewAlpha" "../Abs" "../Perm" "../Rsp" "../Lift" "Quotient_List" "../../Attic/Prove"
begin

atom_decl name

section {*** lam with indirect list recursion ***}

datatype rtrm4 =
  rVr4 "name"
| rAp4 "rtrm4" "rtrm4 list"
| rLm4 "name" "rtrm4"  --"bind (name) in (trm)"

(* there cannot be a clause for lists, as *)
(* permutations are  already defined in Nominal (also functions, options, and so on) *)
ML {*
  val dtinfo = Datatype.the_info @{theory} "Term4.rtrm4";
  val {descr, sorts, ...} = dtinfo;
*}
setup {* snd o (define_raw_perms descr sorts @{thm rtrm4.induct} 1) *}
lemmas perm = permute_rtrm4_permute_rtrm4_list.simps(1-3)
lemma perm_fix:
  fixes ts::"rtrm4 list"
  shows "permute_rtrm4_list p ts = p \<bullet> ts"
  by (induct ts) simp_all
lemmas perm_fixed = perm[simplified perm_fix]

ML {* val bl = [[[BEmy 0], [BEmy 0, BEmy 1], [BSet ([(NONE, 0)], [1])]], [[], [BEmy 0, BEmy 1]]] *}

local_setup {* fn ctxt => let val (_, _, _, ctxt') = define_raw_fvs descr sorts [] bl ctxt in ctxt' end *}
lemmas fv = fv_rtrm4.simps (*fv_rtrm4_list.simps*)

lemma fv_fix: "fv_rtrm4_list = Union o (set o (map fv_rtrm4))"
  by (rule ext) (induct_tac x, simp_all)
lemmas fv_fixed = fv[simplified fv_fix]

(* TODO: check remove 2 *)
local_setup {* snd o (prove_eqvt [@{typ rtrm4},@{typ "rtrm4 list"}] @{thm rtrm4.induct} @{thms perm_fixed fv_rtrm4.simps fv_rtrm4_list.simps} [@{term fv_rtrm4}, @{term fv_rtrm4_list}]) *}
thm eqvts(1-2)

local_setup {* snd o define_raw_alpha dtinfo [] bl [@{term fv_rtrm4}, @{term fv_rtrm4_list}] *}
local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha4_inj}, []), (build_rel_inj @{thms alpha_rtrm4_alpha_rtrm4_list.intros} @{thms rtrm4.distinct rtrm4.inject list.distinct list.inject} @{thms alpha_rtrm4.cases alpha_rtrm4_list.cases} ctxt)) ctxt)) *}
lemmas alpha_inj = alpha4_inj(1-3)

lemma alpha_fix: "alpha_rtrm4_list = list_all2 alpha_rtrm4"
  apply (rule ext)+
  apply (induct_tac x xa rule: list_induct2')
  apply (simp_all add: alpha_rtrm4_alpha_rtrm4_list.intros)
  apply clarify apply (erule alpha_rtrm4_list.cases) apply(simp_all)
  apply clarify apply (erule alpha_rtrm4_list.cases) apply(simp_all)
  apply rule
  apply (erule alpha_rtrm4_list.cases)
  apply simp_all
  apply (rule alpha_rtrm4_alpha_rtrm4_list.intros)
  apply simp_all
  done

lemmas alpha_inj_fixed = alpha_inj[simplified alpha_fix (*fv_fix*)]

notation
    alpha_rtrm4 ("_ \<approx>4 _" [100, 100] 100)
and alpha_rtrm4_list ("_ \<approx>4l _" [100, 100] 100)

declare perm_fixed[eqvt]
equivariance alpha_rtrm4
lemmas alpha4_eqvt = eqvts(1-2)
lemmas alpha4_eqvt_fixed = alpha4_eqvt(2)[simplified alpha_fix (*fv_fix*)]

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha4_reflp}, []),
  build_alpha_refl [((0, @{term alpha_rtrm4}), 0), ((0, @{term alpha_rtrm4_list}), 0)] [@{term alpha_rtrm4}, @{term alpha_rtrm4_list}] @{thm rtrm4.induct} @{thms alpha4_inj} ctxt) ctxt)) *}
thm alpha4_reflp

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha4_equivp}, []),
  (build_equivps [@{term alpha_rtrm4}, @{term alpha_rtrm4_list}] @{thms alpha4_reflp} @{thm alpha_rtrm4_alpha_rtrm4_list.induct} @{thms rtrm4.inject list.inject} @{thms alpha4_inj} @{thms rtrm4.distinct list.distinct} @{thms alpha_rtrm4_list.cases alpha_rtrm4.cases} @{thms alpha4_eqvt} ctxt)) ctxt)) *}
lemmas alpha4_equivp_fixed = alpha4_equivp[simplified alpha_fix fv_fix]

quotient_type
  trm4 = rtrm4 / alpha_rtrm4
  by (simp_all add: alpha4_equivp)

local_setup {*
(fn ctxt => ctxt
 |> snd o (Quotient_Def.quotient_lift_const [] ("Vr4", @{term rVr4}))
 |> snd o (Quotient_Def.quotient_lift_const [@{typ "trm4"}] ("Ap4", @{term rAp4}))
 |> snd o (Quotient_Def.quotient_lift_const [] ("Lm4", @{term rLm4}))
 |> snd o (Quotient_Def.quotient_lift_const [] ("fv_trm4", @{term fv_rtrm4})))
*}
print_theorems


lemma fv_rtrm4_rsp:
  "xa \<approx>4 ya \<Longrightarrow> fv_rtrm4 xa = fv_rtrm4 ya"
  "x \<approx>4l y \<Longrightarrow> fv_rtrm4_list x = fv_rtrm4_list y"
  apply (induct rule: alpha_rtrm4_alpha_rtrm4_list.inducts)
  apply (simp_all add: alpha_gen)
done

local_setup {* snd o prove_const_rsp [] @{binding fv_rtrm4_rsp'} [@{term fv_rtrm4}]
  (fn _ => asm_full_simp_tac (@{simpset} addsimps @{thms fv_rtrm4_rsp}) 1) *}
print_theorems

local_setup {* snd o prove_const_rsp [] @{binding rVr4_rsp} [@{term rVr4}]
  (fn _ => constr_rsp_tac @{thms alpha4_inj} @{thms fv_rtrm4_rsp alpha4_equivp} 1) *}
local_setup {* snd o prove_const_rsp [] @{binding rLm4_rsp} [@{term rLm4}]
  (fn _ => constr_rsp_tac @{thms alpha4_inj} @{thms fv_rtrm4_rsp alpha4_equivp} 1) *}

lemma [quot_respect]:
  "(alpha_rtrm4 ===> list_all2 alpha_rtrm4 ===> alpha_rtrm4) rAp4 rAp4"
  by (simp add: alpha_inj_fixed)

local_setup {* snd o prove_const_rsp [] @{binding permute_rtrm4_rsp}
  [@{term "permute :: perm \<Rightarrow> rtrm4 \<Rightarrow> rtrm4"}]
  (fn _ => asm_simp_tac (HOL_ss addsimps @{thms alpha4_eqvt}) 1) *}

setup {* define_lifted_perms [@{typ trm4}] ["Term4.trm4"] [("permute_trm4", @{term "permute :: perm \<Rightarrow> rtrm4 \<Rightarrow> rtrm4"})] @{thms permute_rtrm4_permute_rtrm4_list_zero permute_rtrm4_permute_rtrm4_list_plus} *}
print_theorems

(* Instead of permute for trm4_list we may need the following 2 lemmas: *)
lemma [quot_preserve]: "(id ---> map rep_trm4 ---> map abs_trm4) permute = permute"
  apply (simp add: expand_fun_eq)
  apply clarify
  apply (rename_tac "pi" x)
  apply (induct_tac x)
  apply simp
  apply simp
  apply (simp add: meta_eq_to_obj_eq[OF permute_trm4_def,simplified expand_fun_eq,simplified])
  done

lemma [quot_respect]: "(op = ===> list_all2 alpha_rtrm4 ===> list_all2 alpha_rtrm4) permute permute"
  apply simp
  apply (rule allI)+
  apply (induct_tac xa y rule: list_induct2')
  apply simp_all
  apply clarify
  apply (erule alpha4_eqvt)
  done

ML {*
  map (lift_thm [@{typ trm4}] @{context}) @{thms perm_fixed}
*}

ML {* lift_thm [@{typ trm4}] @{context} @{thm rtrm4.induct} *}

ML {*
  map (lift_thm [@{typ trm4}] @{context}) @{thms fv_rtrm4.simps[simplified fv_fix] fv_rtrm4_list.simps[simplified fv_fix]}
*}

ML {*
val liftd =
  map (Local_Defs.unfold @{context} @{thms id_simps}) (
    map (Local_Defs.fold @{context} @{thms alphas}) (
      map (lift_thm [@{typ trm4}] @{context}) @{thms alpha_inj_fixed[unfolded alphas]}
    )
  )
*}

ML {*
  map (lift_thm [@{typ trm4}] @{context})
  (flat (map (distinct_rel @{context} @{thms alpha_rtrm4.cases alpha_rtrm4_list.cases}) [(@{thms rtrm4.distinct},@{term "alpha_rtrm4"})]))
*}

thm eqvts(6-7)
ML {*
  map (lift_thm [@{typ trm4}] @{context}) @{thms eqvts(6-7)[simplified fv_fix]}
*}

end
