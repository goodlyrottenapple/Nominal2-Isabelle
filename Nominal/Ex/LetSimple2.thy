theory LetSimple2
imports "../Nominal2" 
begin


atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Let as::"assn" t::"trm"   binds "bn as" in t
and assn =
  Assn "name" "trm"
binder
  bn
where
 "bn (Assn x t) = [atom x]"

print_theorems

thm bn_raw.simps
thm permute_bn_raw.simps
thm trm_assn.perm_bn_alpha
thm trm_assn.permute_bn

thm trm_assn.fv_defs
thm trm_assn.eq_iff 
thm trm_assn.bn_defs
thm trm_assn.bn_inducts
thm trm_assn.perm_simps
thm trm_assn.induct
thm trm_assn.inducts
thm trm_assn.distinct
thm trm_assn.supp
thm trm_assn.fresh
thm trm_assn.exhaust
thm trm_assn.strong_exhaust
thm trm_assn.perm_bn_simps

thm alpha_bn_raw.cases
thm trm_assn.alpha_refl
thm trm_assn.alpha_sym
thm trm_assn.alpha_trans

lemmas alpha_bn_cases[consumes 1] = alpha_bn_raw.cases[quot_lifted]

lemma alpha_bn_refl: "alpha_bn x x"
  by(rule trm_assn.alpha_refl)

lemma alpha_bn_sym: "alpha_bn x y \<Longrightarrow> alpha_bn y x"
  by (rule trm_assn.alpha_sym)

lemma alpha_bn_trans: "alpha_bn x y \<Longrightarrow> alpha_bn y z \<Longrightarrow> alpha_bn x z"
  using trm_assn.alpha_trans by metis

lemma fv_bn_finite[simp]:
  "finite (fv_bn as)"
apply(case_tac as rule: trm_assn.exhaust(2))
apply(simp add: trm_assn.supp finite_supp)
done


lemma k: "A \<Longrightarrow> A \<and> A" by blast



section {* definition with helper functions *}

function 
  apply_assn
where
  "apply_assn f (Assn x t) = (f t)"
apply(case_tac x)
apply(simp)
apply(case_tac b rule: trm_assn.exhaust(2))
apply(blast)
apply(simp)
done

termination
  by lexicographic_order

function 
  apply_assn2
where
  "apply_assn2 f (Assn x t) = Assn x (f t)"
apply(case_tac x)
apply(simp)
apply(case_tac b rule: trm_assn.exhaust(2))
apply(blast)
apply(simp)
done

termination
  by lexicographic_order

lemma [eqvt]:
  shows "p \<bullet> (apply_assn f as) = apply_assn (p \<bullet> f) (p \<bullet> as)"
apply(induct f as rule: apply_assn.induct)
apply(simp)
apply(perm_simp)
apply(rule)
done

lemma [eqvt]:
  shows "p \<bullet> (apply_assn2 f as) = apply_assn2 (p \<bullet> f) (p \<bullet> as)"
apply(induct f as rule: apply_assn.induct)
apply(simp)
apply(perm_simp)
apply(rule)
done


nominal_function
    height_trm :: "trm \<Rightarrow> nat"
where
  "height_trm (Var x) = 1"
| "height_trm (App l r) = max (height_trm l) (height_trm r)"
| "height_trm (Let as b) = max (apply_assn height_trm as) (height_trm b)"
  apply (simp only: eqvt_def height_trm_graph_def)
  apply (rule, perm_simp)
  apply(rule)
  apply(rule TrueI)
  apply (case_tac x rule: trm_assn.exhaust(1))
  apply (auto simp add: alpha_bn_refl)[3]
  apply (drule_tac x="assn" in meta_spec)
  apply (drule_tac x="trm" in meta_spec)
  apply(simp add: alpha_bn_refl)
  apply(simp_all)[5]
  apply(simp)
  apply(erule conjE)+
  apply(erule alpha_bn_cases)
  apply(simp)
  apply (subgoal_tac "height_trm_sumC b = height_trm_sumC ba")
  apply simp
  apply(simp add: trm_assn.bn_defs)
  apply(erule_tac c="()" in Abs_lst_fcb2)
  apply(simp_all add: pure_fresh fresh_star_def)[3]
  apply(simp_all add: eqvt_at_def)
  done

(* assn-function prevents automatic discharge
termination by lexicographic_order
*)

nominal_function 
  subst_trm :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm"  ("_ [_ ::= _]" [90, 90, 90] 90) 
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "(set (bn as)) \<sharp>* (y, s) \<Longrightarrow> 
      (Let as t)[y ::= s] = Let (apply_assn2 (\<lambda>t. t[y ::=s]) as) (t[y ::= s])"
  apply (simp only: eqvt_def subst_trm_graph_def)
  apply (rule, perm_simp)
  apply(rule)
  apply(rule TrueI)
  apply(case_tac x)
  apply(simp)
  apply (rule_tac y="a" and c="(b,c)" in trm_assn.strong_exhaust(1))
  apply (auto simp add: alpha_bn_refl)[3]
  apply(simp_all)[5]
  apply(simp)
  apply(erule conjE)+
  apply(erule alpha_bn_cases)
  apply(simp)
  apply(simp add: trm_assn.bn_defs)
  apply(erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff fresh_star_def)
  apply(simp add: fresh_star_def)
  apply(simp_all add: eqvt_at_def perm_supp_eq fresh_star_Pair)[2]
  done


section {* direct definitions --- problems *}

lemma cheat: "P" sorry

definition
  "eqvt_at_bn f as \<equiv> \<forall>p. (p \<bullet> (f as)) = f (permute_bn p as)"

definition
  "alpha_bn_preserve f as \<equiv> \<forall>p. f as = f (permute_bn p as)"

lemma
  fixes as::"assn"
  assumes "eqvt_at f as"
  shows "eqvt_at_bn f as"
using assms
unfolding eqvt_at_bn_def
apply(rule_tac allI)
apply(drule k)
apply(erule conjE)
apply(subst (asm) eqvt_at_def)
apply(simp)

oops



nominal_function 
<<<<<<< variant A
 (invariant "\<lambda>x y. case x of Inl x1 \<Rightarrow> True | Inr x2 \<Rightarrow> alpha_bn_preserve (height_assn2::assn \<Rightarrow> nat) x2")
>>>>>>> variant B
####### Ancestor
 (invariant "\<lambda>x y. case x of Inl x1 \<Rightarrow> True | Inr x2 \<Rightarrow> \<forall>p. (permute_bn p x2) = x2 \<longrightarrow> (p \<bullet> y) = y")
======= end
    height_trm2 :: "trm \<Rightarrow> nat"
and height_assn2 :: "assn \<Rightarrow> nat"
where
  "height_trm2 (Var x) = 1"
| "height_trm2 (App l r) = max (height_trm2 l) (height_trm2 r)"
| "set (bn as) \<sharp>* fv_bn as \<Longrightarrow> height_trm2 (Let as b) = max (height_assn2 as) (height_trm2 b)"
| "height_assn2 (Assn x t) = (height_trm2 t)"
  thm height_trm2_height_assn2_graph.intros[no_vars]
  thm height_trm2_height_assn2_graph_def
  apply (simp only: eqvt_def height_trm2_height_assn2_graph_def)
  apply (rule, perm_simp, rule)
  -- "invariant"
  apply(simp)
<<<<<<< variant A
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp add: alpha_bn_preserve_def)
  apply(simp add: height_assn2_def)
  apply(simp add: trm_assn.perm_bn_simps)
  apply(rule allI)
  thm height_trm2_height_assn2_graph.intros[no_vars]
  thm height_trm2_height_assn2_sumC_def
  apply(rule cheat)
  apply -
>>>>>>> variant B
####### Ancestor
  apply(simp)
  apply(simp)
  apply(simp)
  apply(rule cheat)
  apply -
======= end
  --"completeness"
  apply (case_tac x)
  apply(simp)
  apply (rule_tac y="a" and c="a" in trm_assn.strong_exhaust(1))
  apply (auto simp add: alpha_bn_refl)[3]
  apply (drule_tac x="assn" in meta_spec)
  apply (drule_tac x="trm" in meta_spec)
  apply(simp add: alpha_bn_refl)
  apply(rotate_tac 3)
  apply(drule meta_mp)
  apply(simp add: fresh_star_def trm_assn.fresh)
  apply(simp add: fresh_def)
  apply(subst supp_finite_atom_set)
  apply(simp)
  apply(simp)
  apply(simp)
  apply (case_tac b rule: trm_assn.exhaust(2))
  apply (auto)[1]
  apply(simp_all)[7]
  prefer 2
  apply(simp)
  prefer 2
  apply(simp)
  --"let case"
  apply (simp only: meta_eq_to_obj_eq[OF height_trm2_def, symmetric, unfolded fun_eq_iff])
  apply (simp only: meta_eq_to_obj_eq[OF height_assn2_def, symmetric, unfolded fun_eq_iff])
  apply (subgoal_tac "eqvt_at height_assn2 as")
  apply (subgoal_tac "eqvt_at height_assn2 asa")
  apply (subgoal_tac "eqvt_at height_trm2 b")
  apply (subgoal_tac "eqvt_at height_trm2 ba")
  apply (thin_tac "eqvt_at height_trm2_height_assn2_sumC (Inr as)")
  apply (thin_tac "eqvt_at height_trm2_height_assn2_sumC (Inr asa)")
  apply (thin_tac "eqvt_at height_trm2_height_assn2_sumC (Inl b)")
  apply (thin_tac "eqvt_at height_trm2_height_assn2_sumC (Inl ba)")
  defer
  apply (simp add: eqvt_at_def height_trm2_def)
  apply (simp add: eqvt_at_def height_trm2_def)
  apply (simp add: eqvt_at_def height_assn2_def)
  apply (simp add: eqvt_at_def height_assn2_def)
  apply (subgoal_tac "height_assn2 as = height_assn2 asa")
  apply (subgoal_tac "height_trm2 b = height_trm2 ba")
  apply simp
  apply(simp)
  apply(erule conjE)+
  apply(erule alpha_bn_cases)
  apply(simp)
  apply(simp add: trm_assn.bn_defs)
  apply(erule_tac c="()" in Abs_lst_fcb2)
  apply(simp_all add: fresh_star_def pure_fresh)[3]
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def)
  apply(drule Inl_inject)
  apply(simp (no_asm_use))
  apply(clarify)
  apply(erule alpha_bn_cases)
  apply(simp del: trm_assn.eq_iff)
  apply(simp only: trm_assn.bn_defs)
<<<<<<< variant A
  apply(erule_tac c="()" in Abs_lst1_fcb2')
  apply(simp_all add: fresh_star_def pure_fresh)[3]
  apply(simp add: eqvt_at_bn_def)
  apply(simp add: trm_assn.perm_bn_simps)
  apply(simp add: eqvt_at_bn_def)
  apply(simp add: trm_assn.perm_bn_simps)
  done
 
>>>>>>> variant B
  apply(erule_tac c="(trm_rawa)" in Abs_lst1_fcb2')
  apply(simp_all add: fresh_star_def pure_fresh)[2]
  apply(simp add: trm_assn.supp)
  apply(simp add: fresh_def)
  apply(subst (asm) supp_finite_atom_set)
  apply(simp add: finite_supp)
  apply(subst (asm) supp_finite_atom_set)
  apply(simp add: finite_supp)
  apply(simp)
  apply(simp add: eqvt_at_def perm_supp_eq)
  apply(simp add: eqvt_at_def perm_supp_eq)
  done
####### Ancestor
  apply(erule_tac c="()" in Abs_lst1_fcb2')
  apply(simp_all add: fresh_star_def pure_fresh)[3]

  oops
======= end

termination by lexicographic_order

lemma ww1:
  shows "finite (fv_trm t)"
  and "finite (fv_bn as)"
apply(induct t and as rule: trm_assn.inducts)
apply(simp_all add: trm_assn.fv_defs supp_at_base)
done

text {* works, but only because no recursion in as *}

nominal_function (invariant "\<lambda>x (y::atom set). finite y")
  frees_set :: "trm \<Rightarrow> atom set"
where
  "frees_set (Var x) = {atom x}"
| "frees_set (App t1 t2) = frees_set t1 \<union> frees_set t2"
| "frees_set (Let as t) = (frees_set t) - (set (bn as)) \<union> (fv_bn as)"
  apply(simp add: eqvt_def frees_set_graph_def)
  apply(rule, perm_simp, rule)
  apply(erule frees_set_graph.induct)
  apply(auto simp add: ww1)[3]
  apply(rule_tac y="x" in trm_assn.exhaust(1))
  apply(auto simp add: alpha_bn_refl)[3]
  apply(drule_tac x="assn" in meta_spec)
  apply(drule_tac x="trm" in meta_spec)
  apply(simp add: alpha_bn_refl)
  apply(simp_all)[5]
  apply(simp)
  apply(erule conjE)
  apply(erule alpha_bn_cases)
  apply(simp add: trm_assn.bn_defs)
  apply(simp add: trm_assn.fv_defs)
  (* apply(erule_tac c="(trm_rawa)" in Abs_lst1_fcb2) *)
  apply(subgoal_tac " frees_set_sumC t - {atom name} = frees_set_sumC ta - {atom namea}")
  apply(simp)
  apply(erule_tac c="()" in Abs_lst1_fcb2)
  apply(simp add: fresh_minus_atom_set)
  apply(simp add: fresh_star_def fresh_Unit)
  apply(simp add: Diff_eqvt eqvt_at_def, perm_simp, rule refl)
  apply(simp add: Diff_eqvt eqvt_at_def, perm_simp, rule refl)
  done

termination
  by lexicographic_order

lemma test:
  assumes a: "\<exists>y. f x = Inl y"
  shows "(p \<bullet> (Sum_Type.Projl (f x))) = Sum_Type.Projl ((p \<bullet> f) (p \<bullet> x))"
using a
apply clarify
apply(frule_tac p="p" in permute_boolI)
apply(simp (no_asm_use) only: eqvts)
apply(subst (asm) permute_fun_app_eq)
back
apply(simp)
done


nominal_function (default "sum_case (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)")
  subst_trm2 :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm"  ("_ [_ ::trm2= _]" [90, 90, 90] 90) and
  subst_assn2 :: "assn \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> assn"  ("_ [_ ::assn2= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::trm2= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::trm2= s] = App (t1[y ::trm2= s]) (t2[y ::trm2= s])"
| "(set (bn as)) \<sharp>* (y, s, fv_bn as) \<Longrightarrow> (Let as t)[y ::trm2= s] = Let (ast[y ::assn2= s]) (t[y ::trm2= s])"
| "(Assn x t)[y ::assn2= s] = Assn x (t[y ::trm2= s])"
apply(subgoal_tac "\<And>p x r. subst_trm2_subst_assn2_graph x r \<Longrightarrow> subst_trm2_subst_assn2_graph (p \<bullet> x) (p \<bullet> r)")
apply(simp add: eqvt_def)
apply(rule allI)
apply(simp add: permute_fun_def permute_bool_def)
apply(rule ext)
apply(rule ext)
apply(rule iffI)
apply(drule_tac x="p" in meta_spec)
apply(drule_tac x="- p \<bullet> x" in meta_spec)
apply(drule_tac x="- p \<bullet> xa" in meta_spec)
apply(simp)
apply(drule_tac x="-p" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(simp)
--"Eqvt One way"
defer
  apply(rule TrueI)
  apply(case_tac x)
  apply(simp)
  apply(case_tac a)
  apply(simp)
  apply(rule_tac y="aa" and c="(b, c, aa)" in trm_assn.strong_exhaust(1))
  apply(blast)+
  apply(simp)
  apply(drule_tac x="assn" in meta_spec)
  apply(drule_tac x="b" in meta_spec)
  apply(drule_tac x="c" in meta_spec)
  apply(drule_tac x="trm" in meta_spec)
  apply(simp add: trm_assn.alpha_refl)
  apply(rotate_tac 5)
  apply(drule meta_mp)
  apply(simp add: fresh_star_Pair)
  apply(simp add: fresh_star_def trm_assn.fresh)
  apply(simp add: fresh_def)
  apply(subst supp_finite_atom_set)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(case_tac b)
  apply(simp)
  apply(rule_tac y="a" in trm_assn.exhaust(2))
  apply(simp)
  apply(blast)
--"compatibility" 
  apply(all_trivials)
  apply(simp)
  apply(simp)
  prefer 2
  apply(simp)
  apply(drule Inl_inject)
  apply(rule arg_cong)
  back
  apply (simp only: meta_eq_to_obj_eq[OF subst_trm2_def, symmetric, unfolded fun_eq_iff])
  apply (simp only: meta_eq_to_obj_eq[OF subst_assn2_def, symmetric, unfolded fun_eq_iff])
  apply (subgoal_tac "eqvt_at (\<lambda>ast. subst_assn2 ast ya sa) ast")
  apply (subgoal_tac "eqvt_at (\<lambda>asta. subst_assn2 asta ya sa) asta")
  apply (subgoal_tac "eqvt_at (\<lambda>t. subst_trm2 t ya sa) t")
  apply (subgoal_tac "eqvt_at (\<lambda>ta. subst_trm2 ta ya sa) ta")
  apply (thin_tac "eqvt_at subst_trm2_subst_assn2_sumC (Inr (ast, y, s))")
  apply (thin_tac "eqvt_at subst_trm2_subst_assn2_sumC (Inr (asta, ya, sa))")
  apply (thin_tac "eqvt_at subst_trm2_subst_assn2_sumC (Inl (t, y, s))")
  apply (thin_tac "eqvt_at subst_trm2_subst_assn2_sumC (Inl (ta, ya, sa))")
  apply(simp)
  (* HERE *)
  apply (subgoal_tac "subst_assn2 ast y s= subst_assn2 asta ya sa")
  apply (subgoal_tac "subst_trm2 t y s = subst_trm2 ta ya sa")
  apply(simp)
  apply(simp)
  apply(erule_tac conjE)+
  apply(erule alpha_bn_cases)
  apply(simp add: trm_assn.bn_defs)
  apply(rotate_tac 7)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(erule fresh_eqvt_at)
  
  
  thm fresh_eqvt_at
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)



  apply(simp_all add: fresh_star_def fresh_Pair_elim)[1]
  apply(blast)
  apply(simp_all)[5]
  apply(simp (no_asm_use))
  apply(simp)
  apply(erule conjE)+
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
done


end
