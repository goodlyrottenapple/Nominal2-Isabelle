theory Term1
imports "Nominal2_Atoms" "Nominal2_Eqvt" "Nominal2_Supp" "Abs" "Perm" "Fv" "Rsp" "../Attic/Prove"
begin

atom_decl name

section {*** lets with binding patterns ***}

datatype rtrm1 =
  rVr1 "name"
| rAp1 "rtrm1" "rtrm1"
| rLm1 "name" "rtrm1"        --"name is bound in trm1"
| rLt1 "bp" "rtrm1" "rtrm1"   --"all variables in bp are bound in the 2nd trm1"
and bp =
  BUnit
| BVr "name"
| BPr "bp" "bp"

print_theorems

(* to be given by the user *)

primrec 
  bv1
where
  "bv1 (BUnit) = {}"
| "bv1 (BVr x) = {atom x}"
| "bv1 (BPr bp1 bp2) = (bv1 bp1) \<union> (bv1 bp2)"

setup {* snd o define_raw_perms (Datatype.the_info @{theory} "Term1.rtrm1") 2 *}
thm permute_rtrm1_permute_bp.simps

local_setup {*
  snd o define_fv_alpha (Datatype.the_info @{theory} "Term1.rtrm1")
  [[[], [], [(NONE, 0, 1)], [(SOME (@{term bv1}, true), 0, 2)]],
  [[], [], []]] [(@{term bv1}, 1, [[], [0], [0, 1]])] *}

notation
  alpha_rtrm1 ("_ \<approx>1 _" [100, 100] 100) and
  alpha_bp ("_ \<approx>1b _" [100, 100] 100)
thm alpha_rtrm1_alpha_bp_alpha_bv1.intros
(*thm fv_rtrm1_fv_bp.simps[no_vars]*)

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha1_inj}, []), (build_alpha_inj @{thms alpha_rtrm1_alpha_bp_alpha_bv1.intros} @{thms rtrm1.distinct rtrm1.inject bp.distinct bp.inject} @{thms alpha_rtrm1.cases alpha_bp.cases alpha_bv1.cases} ctxt)) ctxt)) *}
thm alpha1_inj

local_setup {*
snd o (build_eqvts @{binding bv1_eqvt} [@{term bv1}] (build_eqvts_tac @{thm rtrm1_bp.inducts(2)} @{thms bv1.simps permute_rtrm1_permute_bp.simps} @{context}))
*}

local_setup {*
snd o build_eqvts @{binding fv_rtrm1_fv_bp_eqvt} [@{term fv_rtrm1}, @{term fv_bp}] (build_eqvts_tac @{thm rtrm1_bp.induct} @{thms fv_rtrm1_fv_bp.simps permute_rtrm1_permute_bp.simps} @{context})
*}

(*local_setup {*
snd o build_eqvts @{binding fv_rtrm1_fv_bv1_eqvt} [@{term fv_rtrm1}, @{term fv_bv1}] (build_eqvts_tac @{thm rtrm1_bp.induct} @{thms fv_rtrm1_fv_bv1.simps permute_rtrm1_permute_bp.simps} @{context})
*}
print_theorems

local_setup {*
snd o build_eqvts @{binding fv_bp_eqvt} [@{term fv_bp}] (build_eqvts_tac @{thm rtrm1_bp.inducts(2)} @{thms fv_rtrm1_fv_bv1.simps fv_bp.simps permute_rtrm1_permute_bp.simps} @{context})
*}
print_theorems
*)

local_setup {*
(fn ctxt => snd (Local_Theory.note ((@{binding alpha1_eqvt}, []),
build_alpha_eqvts [@{term alpha_rtrm1}, @{term alpha_bp}, @{term alpha_bv1}] (fn _ => alpha_eqvt_tac @{thm alpha_rtrm1_alpha_bp_alpha_bv1.induct} @{thms permute_rtrm1_permute_bp.simps alpha1_inj} ctxt 1) ctxt) ctxt)) *}

lemma alpha1_eqvt_proper[eqvt]:
  "pi \<bullet> (t \<approx>1 s) = ((pi \<bullet> t) \<approx>1 (pi \<bullet> s))"
  "pi \<bullet> (alpha_bp a b) = (alpha_bp (pi \<bullet> a) (pi \<bullet> b))"
  apply (simp_all only: eqvts)
  apply rule
  apply (simp_all add: alpha1_eqvt)
  apply (subst permute_minus_cancel(2)[symmetric,of "t" "pi"])
  apply (subst permute_minus_cancel(2)[symmetric,of "s" "pi"])
  apply (simp_all only: alpha1_eqvt)
  apply rule
  apply (simp_all add: alpha1_eqvt)
  apply (subst permute_minus_cancel(2)[symmetric,of "a" "pi"])
  apply (subst permute_minus_cancel(2)[symmetric,of "b" "pi"])
  apply (simp_all only: alpha1_eqvt)
done
thm eqvts_raw(1)

lemma "(b \<approx>1 a \<longrightarrow> a \<approx>1 b) \<and> (x \<approx>1b y \<longrightarrow> y \<approx>1b x) \<and> (alpha_bv1 x y \<longrightarrow> alpha_bv1 y x)"
apply (tactic {* symp_tac @{thm alpha_rtrm1_alpha_bp_alpha_bv1.induct} @{thms alpha1_inj} @{thms alpha1_eqvt} @{context} 1 *})
done

lemma alpha1_equivp:
  "equivp alpha_rtrm1"
  "equivp alpha_bp"
sorry

(*
local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha1_equivp}, []),
  (build_equivps [@{term alpha_rtrm1}, @{term alpha_bp}, @{term alpha_bv1}] @{thm rtrm1_bp.induct} @{thm alpha_rtrm1_alpha_bp_alpha_bv1.induct} @{thms rtrm1.inject bp.inject} @{thms alpha1_inj} @{thms rtrm1.distinct bp.distinct} @{thms alpha_rtrm1.cases alpha_bp.cases} @{thms alpha1_eqvt} ctxt)) ctxt)) *}
thm alpha1_equivp*)

local_setup  {* define_quotient_type [(([], @{binding trm1}, NoSyn), (@{typ rtrm1}, @{term alpha_rtrm1}))]
  (rtac @{thm alpha1_equivp(1)} 1) *}

local_setup {*
(fn ctxt => ctxt
 |> snd o (Quotient_Def.quotient_lift_const ("Vr1", @{term rVr1}))
 |> snd o (Quotient_Def.quotient_lift_const ("Ap1", @{term rAp1}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lm1", @{term rLm1}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lt1", @{term rLt1}))
 |> snd o (Quotient_Def.quotient_lift_const ("fv_trm1", @{term fv_rtrm1})))
*}
print_theorems

local_setup {* snd o prove_const_rsp @{binding fv_rtrm1_rsp} [@{term fv_rtrm1}]
  (fn _ => Skip_Proof.cheat_tac @{theory}) *}
local_setup {* snd o prove_const_rsp @{binding rVr1_rsp} [@{term rVr1}]
  (fn _ => constr_rsp_tac @{thms alpha1_inj} @{thms fv_rtrm1_rsp} @{thms alpha1_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rAp1_rsp} [@{term rAp1}]
  (fn _ => constr_rsp_tac @{thms alpha1_inj} @{thms fv_rtrm1_rsp} @{thms alpha1_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rLm1_rsp} [@{term rLm1}]
  (fn _ => constr_rsp_tac @{thms alpha1_inj} @{thms fv_rtrm1_rsp} @{thms alpha1_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rLt1_rsp} [@{term rLt1}]
  (fn _ => Skip_Proof.cheat_tac @{theory}) *}
local_setup {* snd o prove_const_rsp @{binding permute_rtrm1_rsp} [@{term "permute :: perm \<Rightarrow> rtrm1 \<Rightarrow> rtrm1"}]
  (fn _ => asm_simp_tac (HOL_ss addsimps @{thms alpha1_eqvt}) 1) *}

lemmas trm1_bp_induct = rtrm1_bp.induct[quot_lifted]
lemmas trm1_bp_inducts = rtrm1_bp.inducts[quot_lifted]

setup {* define_lifted_perms ["Term1.trm1"] [("permute_trm1", @{term "permute :: perm \<Rightarrow> rtrm1 \<Rightarrow> rtrm1"})]
  @{thms permute_rtrm1_permute_bp_zero permute_rtrm1_permute_bp_append} *}

lemmas
    permute_trm1 = permute_rtrm1_permute_bp.simps[quot_lifted]
and fv_trm1 = fv_rtrm1_fv_bp.simps[quot_lifted]
and fv_trm1_eqvt = fv_rtrm1_fv_bp_eqvt[quot_lifted]
and alpha1_INJ = alpha1_inj[unfolded alpha_gen2, unfolded alpha_gen, quot_lifted, folded alpha_gen2, folded alpha_gen]

lemma supports:
  "(supp (atom x)) supports (Vr1 x)"
  "(supp t \<union> supp s) supports (Ap1 t s)"
  "(supp (atom x) \<union> supp t) supports (Lm1 x t)"
  "(supp b \<union> supp t \<union> supp s) supports (Lt1 b t s)"
  "{} supports BUnit"
  "(supp (atom x)) supports (BVr x)"
  "(supp a \<union> supp b) supports (BPr a b)"
apply(tactic {* ALLGOALS (supports_tac @{thms permute_trm1}) *})
done

prove rtrm1_bp_fs: {* snd (mk_fs [@{typ trm1}, @{typ bp}]) *}
apply (tactic {* fs_tac @{thm trm1_bp_induct} @{thms supports} 1 *})
done

instance trm1 and bp :: fs
apply default
apply (simp_all add: rtrm1_bp_fs)
done

lemma fv_eq_bv_pre: "fv_bp bp = bv1 bp"
apply(induct bp rule: trm1_bp_inducts(2))
apply(simp_all)
done

lemma fv_eq_bv: "fv_bp = bv1"
apply(rule ext)
apply(rule fv_eq_bv_pre)
done

lemma helper2: "{b. \<forall>pi. pi \<bullet> (a \<rightleftharpoons> b) \<bullet> bp \<noteq> bp} = {}"
apply auto
apply (rule_tac x="(x \<rightleftharpoons> a)" in exI)
apply auto
done

lemma alpha_bp_eq_eq: "alpha_bp a b = (a = b)"
apply rule
apply (induct a b rule: alpha_rtrm1_alpha_bp_alpha_bv1.inducts(2))
apply (simp_all add: equivp_reflp[OF alpha1_equivp(2)])
done

lemma alpha_bp_eq: "alpha_bp = (op =)"
apply (rule ext)+
apply (rule alpha_bp_eq_eq)
done

lemma ex_out: 
  "(\<exists>x. Z x \<and> Q) = (Q \<and> (\<exists>x. Z x))"
  "(\<exists>x. Q \<and> Z x) = (Q \<and> (\<exists>x. Z x))"
  "(\<exists>x. P x \<and> Q \<and> Z x) = (Q \<and> (\<exists>x. P x \<and> Z x))"
  "(\<exists>x. Q \<and> P x \<and> Z x) = (Q \<and> (\<exists>x. P x \<and> Z x))"
  "(\<exists>x. Q \<and> P x \<and> Z x \<and> W x) = (Q \<and> (\<exists>x. P x \<and> Z x \<and> W x))"
apply (blast)+
done

lemma Collect_neg_conj: "{x. \<not>(P x \<and> Q x)} = {x. \<not>(P x)} \<union> {x. \<not>(Q x)}"
by (simp add: Collect_imp_eq Collect_neg_eq[symmetric])

lemma supp_fv_let:
  assumes sa : "fv_bp bp = supp bp"
  shows "\<lbrakk>fv_trm1 ta = supp ta; fv_trm1 tb = supp tb; fv_bp bp = supp bp\<rbrakk>
       \<Longrightarrow> supp (Lt1 bp ta tb) = supp ta \<union> (supp (bp, tb) - supp bp)"
apply(fold supp_Abs)
apply(simp (no_asm) only: fv_trm1 fv_eq_bv sa[simplified fv_eq_bv,symmetric])
apply(simp (no_asm) only: supp_def)
apply(simp only: permute_set_eq permute_trm1)
apply(simp only: alpha1_INJ alpha_bp_eq)
apply(simp only: ex_out)
apply(simp only: Collect_neg_conj)
apply(simp only: permute_ABS)
apply(simp only: Abs_eq_iff)
apply(simp only: alpha_gen supp_Pair split_conv eqvts)
apply(simp only: infinite_Un)
apply(simp only: Collect_disj_eq)
apply(tactic {* Cong_Tac.cong_tac @{thm cong} 1 *}) apply(rule refl)
apply (simp only: eqvts[symmetric] fv_trm1_eqvt[symmetric])
apply (simp only: eqvts Pair_eq)
done

lemma supp_fv:
  "supp t = fv_trm1 t"
  "supp b = fv_bp b"
apply(induct t and b rule: trm1_bp_inducts)
apply(simp_all)
apply(simp add: supp_def permute_trm1 alpha1_INJ fv_trm1)
apply(simp only: supp_at_base[simplified supp_def])
apply(simp add: supp_def permute_trm1 alpha1_INJ fv_trm1)
apply(simp add: Collect_imp_eq Collect_neg_eq Un_commute)
apply(subgoal_tac "supp (Lm1 name rtrm1) = supp (Abs {atom name} rtrm1)")
apply(simp add: supp_Abs fv_trm1)
apply(simp (no_asm) add: supp_def permute_set_eq atom_eqvt permute_trm1)
apply(simp add: alpha1_INJ)
apply(simp add: Abs_eq_iff)
apply(simp add: alpha_gen.simps)
apply(simp add: supp_eqvt[symmetric] fv_trm1_eqvt[symmetric])
apply(simp add: supp_fv_let fv_trm1 fv_eq_bv supp_Pair)
apply blast
apply(simp add: supp_def permute_trm1 alpha1_INJ fv_trm1)
apply(simp add: supp_def permute_trm1 alpha1_INJ fv_trm1)
apply(simp only: supp_at_base[simplified supp_def])
apply(simp (no_asm) only: supp_def permute_set_eq atom_eqvt permute_trm1 alpha1_INJ[simplified alpha_bp_eq])
apply(simp add: Collect_imp_eq Collect_neg_eq[symmetric])
apply(fold supp_def)
apply simp
done

lemma trm1_supp:
  "supp (Vr1 x) = {atom x}"
  "supp (Ap1 t1 t2) = supp t1 \<union> supp t2"
  "supp (Lm1 x t) = (supp t) - {atom x}"
  "supp (Lt1 b t s) = supp t \<union> (supp s - bv1 b)"
by (simp_all add: supp_fv fv_trm1 fv_eq_bv)

lemma trm1_induct_strong:
  assumes "\<And>name b. P b (Vr1 name)"
  and     "\<And>rtrm11 rtrm12 b. \<lbrakk>\<And>c. P c rtrm11; \<And>c. P c rtrm12\<rbrakk> \<Longrightarrow> P b (Ap1 rtrm11 rtrm12)"
  and     "\<And>name rtrm1 b. \<lbrakk>\<And>c. P c rtrm1; (atom name) \<sharp> b\<rbrakk> \<Longrightarrow> P b (Lm1 name rtrm1)"
  and     "\<And>bp rtrm11 rtrm12 b. \<lbrakk>\<And>c. P c rtrm11; \<And>c. P c rtrm12; bv1 bp \<sharp>* b\<rbrakk> \<Longrightarrow> P b (Lt1 bp rtrm11 rtrm12)"
  shows   "P a rtrma"
sorry

end
