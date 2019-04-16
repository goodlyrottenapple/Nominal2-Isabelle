theory Term5
imports "../Nominal2_Atoms" "../Nominal2_Eqvt" "../Nominal2_Supp" "../Abs" "../Perm" "../Fv" "../Rsp"
begin

atom_decl name

datatype rtrm5 =
  rVr5 "name"
| rAp5 "rtrm5" "rtrm5"
| rLt5 "rlts" "rtrm5" --"bind (bv5 lts) in (rtrm5)"
and rlts =
  rLnil
| rLcons "name" "rtrm5" "rlts"

primrec
  rbv5
where
  "rbv5 rLnil = {}"
| "rbv5 (rLcons n t ltl) = {atom n} \<union> (rbv5 ltl)"


setup {* snd o define_raw_perms (Datatype.the_info @{theory} "Term5.rtrm5") 2 *}
print_theorems

local_setup {* snd o define_fv_alpha (Datatype.the_info @{theory} "Term5.rtrm5")
  [[[], [], [(SOME (@{term rbv5}, false), 0, 1)]], [[], []]] [(@{term rbv5}, 1, [[], [(0,NONE), (2,SOME @{term rbv5})]])] *}
print_theorems

notation
  alpha_rtrm5 ("_ \<approx>5 _" [100, 100] 100) and
  alpha_rlts ("_ \<approx>l _" [100, 100] 100)
thm alpha_rtrm5_alpha_rlts_alpha_rbv5.intros

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha5_inj}, []), (build_rel_inj @{thms alpha_rtrm5_alpha_rlts_alpha_rbv5.intros} @{thms rtrm5.distinct rtrm5.inject rlts.distinct rlts.inject} @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases} ctxt)) ctxt)) *}
thm alpha5_inj

lemma rbv5_eqvt[eqvt]:
  "pi \<bullet> (rbv5 x) = rbv5 (pi \<bullet> x)"
  apply (induct x)
  apply (simp_all add: eqvts atom_eqvt)
  done

lemma fv_rtrm5_rlts_eqvt[eqvt]:
  "pi \<bullet> (fv_rtrm5 x) = fv_rtrm5 (pi \<bullet> x)"
  "pi \<bullet> (fv_rlts l) = fv_rlts (pi \<bullet> l)"
  "pi \<bullet> (fv_rbv5 l) = fv_rbv5 (pi \<bullet> l)"
  apply (induct x and l)
  apply (simp_all add: eqvts atom_eqvt)
  done

local_setup {*
(fn ctxt => snd (Local_Theory.note ((@{binding alpha5_eqvt}, []),
build_alpha_eqvts [@{term alpha_rtrm5}, @{term alpha_rlts}, @{term alpha_rbv5}] (fn _ => alpha_eqvt_tac  @{thm alpha_rtrm5_alpha_rlts_alpha_rbv5.induct} @{thms alpha5_inj permute_rtrm5_permute_rlts.simps} ctxt 1) ctxt) ctxt)) *}
print_theorems

lemma alpha5_reflp:
"y \<approx>5 y \<and> (x \<approx>l x \<and> alpha_rbv5 x x)"
apply (rule rtrm5_rlts.induct)
apply (simp_all add: alpha5_inj)
apply (rule_tac x="0::perm" in exI)
apply (simp add: eqvts alpha_gen fresh_star_def fresh_zero_perm)
done

lemma alpha5_symp:
"(a \<approx>5 b \<longrightarrow> b \<approx>5 a) \<and>
(x \<approx>l y \<longrightarrow> y \<approx>l x) \<and>
(alpha_rbv5 x y \<longrightarrow> alpha_rbv5 y x)"
apply (rule alpha_rtrm5_alpha_rlts_alpha_rbv5.induct)
apply (simp_all add: alpha5_inj)
apply (erule conjE)+
apply (erule exE)
apply (rule_tac x="-pi" in exI)
apply (rule alpha_gen_sym)
apply (simp add: alphas)
apply (simp add: alpha5_eqvt)
apply (simp add: alphas)
apply clarify
apply simp
done

lemma alpha5_transp:
"(a \<approx>5 b \<longrightarrow> (\<forall>c. b \<approx>5 c \<longrightarrow> a \<approx>5 c)) \<and>
(x \<approx>l y \<longrightarrow> (\<forall>z. y \<approx>l z \<longrightarrow> x \<approx>l z)) \<and>
(alpha_rbv5 k l \<longrightarrow> (\<forall>m. alpha_rbv5 l m \<longrightarrow> alpha_rbv5 k m))"
apply (rule alpha_rtrm5_alpha_rlts_alpha_rbv5.induct)
apply (rule_tac [!] allI)
apply (simp_all add: alpha5_inj)
apply (tactic {* (imp_elim_tac @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases} @{context}) 1 *})
apply (simp_all add: alpha5_inj)
defer
apply (tactic {* (imp_elim_tac @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases} @{context}) 1 *})
apply (simp_all add: alpha5_inj)
apply (tactic {* (imp_elim_tac @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases} @{context}) 1 *})
apply (simp_all add: alpha5_inj)
apply (tactic {* (imp_elim_tac @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases} @{context}) 1 *})
apply (simp_all add: alpha5_inj)
apply (erule conjE)+
apply (erule exE)+
apply (rule_tac x="pi + pia" in exI)
apply (rule alpha_gen_trans)
prefer 6
apply assumption
apply (simp_all add: alphas alpha5_eqvt)
apply (clarify)
apply simp
done

lemma alpha5_equivp:
  "equivp alpha_rtrm5"
  "equivp alpha_rlts"
  unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
  apply (simp_all only: alpha5_reflp)
  apply (meson alpha5_symp alpha5_transp)
  apply (meson alpha5_symp alpha5_transp)
  done

quotient_type
  trm5 = rtrm5 / alpha_rtrm5
and
  lts = rlts / alpha_rlts
  by (auto intro: alpha5_equivp)

local_setup {*
(fn ctxt => ctxt
 |> snd o (Quotient_Def.quotient_lift_const ("Vr5", @{term rVr5}))
 |> snd o (Quotient_Def.quotient_lift_const ("Ap5", @{term rAp5}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lt5", @{term rLt5}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lnil", @{term rLnil}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lcons", @{term rLcons}))
 |> snd o (Quotient_Def.quotient_lift_const ("fv_trm5", @{term fv_rtrm5}))
 |> snd o (Quotient_Def.quotient_lift_const ("fv_lts", @{term fv_rlts}))
 |> snd o (Quotient_Def.quotient_lift_const ("fv_bv5", @{term fv_rbv5}))
 |> snd o (Quotient_Def.quotient_lift_const ("bv5", @{term rbv5}))
 |> snd o (Quotient_Def.quotient_lift_const ("alpha_bv5", @{term alpha_rbv5})))
*}
print_theorems

lemma alpha5_rfv:
  "(t \<approx>5 s \<Longrightarrow> fv_rtrm5 t = fv_rtrm5 s)"
  "(l \<approx>l m \<Longrightarrow> (fv_rlts l = fv_rlts m \<and> fv_rbv5 l = fv_rbv5 m))"
  "(alpha_rbv5 b c \<Longrightarrow> fv_rbv5 b = fv_rbv5 c)"
  apply(induct rule: alpha_rtrm5_alpha_rlts_alpha_rbv5.inducts)
  apply(simp_all)
  apply(simp add: alpha_gen)
  done

lemma bv_list_rsp:
  shows "x \<approx>l y \<Longrightarrow> rbv5 x = rbv5 y"
  apply(induct rule: alpha_rtrm5_alpha_rlts_alpha_rbv5.inducts(2))
  apply(simp_all)
  apply(clarify)
  apply simp
  done

local_setup {* snd o Local_Theory.note ((@{binding alpha_dis}, []), (flat (map (distinct_rel @{context} @{thms alpha_rtrm5.cases alpha_rlts.cases alpha_rbv5.cases}) [(@{thms rtrm5.distinct}, @{term alpha_rtrm5}), (@{thms rlts.distinct}, @{term alpha_rlts}), (@{thms rlts.distinct}, @{term alpha_rbv5})]))) *}
print_theorems

local_setup {* snd o Local_Theory.note ((@{binding alpha_bn_rsp}, []), prove_alpha_bn_rsp [@{term alpha_rtrm5}, @{term alpha_rlts}] @{thms alpha_rtrm5_alpha_rlts_alpha_rbv5.inducts} @{thms alpha5_inj alpha_dis} @{thms alpha5_equivp} @{context} (@{term alpha_rbv5}, 1)) *}
thm alpha_bn_rsp


lemma [quot_respect]:
  "(alpha_rlts ===> op =) fv_rlts fv_rlts"
  "(alpha_rlts ===> op =) fv_rbv5 fv_rbv5"
  "(alpha_rtrm5 ===> op =) fv_rtrm5 fv_rtrm5"
  "(alpha_rlts ===> op =) rbv5 rbv5"
  "(op = ===> alpha_rtrm5) rVr5 rVr5"
  "(alpha_rtrm5 ===> alpha_rtrm5 ===> alpha_rtrm5) rAp5 rAp5"
  "(alpha_rlts ===> alpha_rtrm5 ===> alpha_rtrm5) rLt5 rLt5"
  "(op = ===> alpha_rtrm5 ===> alpha_rlts ===> alpha_rlts) rLcons rLcons"
  "(op = ===> alpha_rtrm5 ===> alpha_rtrm5) permute permute"
  "(op = ===> alpha_rlts ===> alpha_rlts) permute permute"
  "(alpha_rlts ===> alpha_rlts ===> op =) alpha_rbv5 alpha_rbv5"
  apply (simp_all add: alpha5_inj alpha5_rfv alpha5_eqvt bv_list_rsp alpha5_reflp alpha_bn_rsp)
  apply (clarify)
  apply (rule_tac x="0" in exI) apply (simp add: fresh_star_def fresh_zero_perm alpha_gen alpha5_rfv)
done

lemma
  shows "(alpha_rlts ===> op =) rbv5 rbv5"
  by (simp add: bv_list_rsp)

lemmas trm5_lts_inducts = rtrm5_rlts.inducts[quot_lifted]

instantiation trm5 and lts :: pt
begin

quotient_definition
  "permute_trm5 :: perm \<Rightarrow> trm5 \<Rightarrow> trm5"
is
  "permute :: perm \<Rightarrow> rtrm5 \<Rightarrow> rtrm5"

quotient_definition
  "permute_lts :: perm \<Rightarrow> lts \<Rightarrow> lts"
is
  "permute :: perm \<Rightarrow> rlts \<Rightarrow> rlts"

instance by default
  (simp_all add: permute_rtrm5_permute_rlts_zero[quot_lifted] permute_rtrm5_permute_rlts_append[quot_lifted])

end

lemmas permute_trm5_lts = permute_rtrm5_permute_rlts.simps[quot_lifted]
lemmas bv5[simp] = rbv5.simps[quot_lifted]
lemmas fv_trm5_bv5[simp] = fv_rtrm5_fv_rbv5.simps[quot_lifted]
lemmas fv_lts[simp] = fv_rlts.simps[quot_lifted]
lemmas alpha5_INJ = alpha5_inj[unfolded alpha_gen, quot_lifted, folded alpha_gen]

end
