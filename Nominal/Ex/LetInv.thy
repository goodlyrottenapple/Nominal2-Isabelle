theory Let
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"    binds  x in t
| Let as::"assn" t::"trm"   binds "bn as" in t
and assn =
  ANil
| ACons "name" "trm" "assn"
binder
  bn
where
  "bn ANil = []"
| "bn (ACons x t as) = (atom x) # (bn as)"

print_theorems

thm alpha_trm_raw_alpha_assn_raw_alpha_bn_raw.intros
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

lemma alpha_bn_inducts_raw[consumes 1]:
  "\<lbrakk>alpha_bn_raw a b; P3 ANil_raw ANil_raw;
 \<And>trm_raw trm_rawa assn_raw assn_rawa name namea.
    \<lbrakk>alpha_trm_raw trm_raw trm_rawa; alpha_bn_raw assn_raw assn_rawa;
     P3 assn_raw assn_rawa\<rbrakk>
    \<Longrightarrow> P3 (ACons_raw name trm_raw assn_raw)
        (ACons_raw namea trm_rawa assn_rawa)\<rbrakk> \<Longrightarrow> P3 a b"
  by (erule alpha_trm_raw_alpha_assn_raw_alpha_bn_raw.inducts(3)[of _ _ "\<lambda>x y. True" _ "\<lambda>x y. True", simplified]) auto

lemmas alpha_bn_inducts[consumes 1] = alpha_bn_inducts_raw[quot_lifted]



lemma alpha_bn_refl: "alpha_bn x x"
  by (induct x rule: trm_assn.inducts(2))
     (rule TrueI, auto simp add: trm_assn.eq_iff)
lemma alpha_bn_sym: "alpha_bn x y \<Longrightarrow> alpha_bn y x"
  sorry
lemma alpha_bn_trans: "alpha_bn x y \<Longrightarrow> alpha_bn y z \<Longrightarrow> alpha_bn x z"
  sorry

lemma bn_inj[rule_format]:
  assumes a: "alpha_bn x y"
  shows "bn x = bn y \<longrightarrow> x = y"
  by (rule alpha_bn_inducts[OF a]) (simp_all add: trm_assn.bn_defs)

lemma bn_inj2:
  assumes a: "alpha_bn x y"
  shows "\<And>q r. (q \<bullet> bn x) = (r \<bullet> bn y) \<Longrightarrow> permute_bn q x = permute_bn r y"
using a
apply(induct rule: alpha_bn_inducts)
apply(simp add: trm_assn.perm_bn_simps)
apply(simp add: trm_assn.perm_bn_simps)
apply(simp add: trm_assn.bn_defs)
apply(simp add: atom_eqvt)
done

lemma Abs_lst_fcb2:
  fixes as bs :: "atom list"
    and x y :: "'b :: fs"
    and c::"'c::fs"
  assumes eq: "[as]lst. x = [bs]lst. y"
  and fcb1: "(set as) \<sharp>* c \<Longrightarrow> (set as) \<sharp>* f as x c"
  and fresh1: "set as \<sharp>* c"
  and fresh2: "set bs \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f as x c) = f (p \<bullet> as) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f bs y c) = f (p \<bullet> bs) (p \<bullet> y) c"
  shows "f as x c = f bs y c"
proof -
  have "supp (as, x, c) supports (f as x c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm1 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin1: "finite (supp (f as x c))"
    by (auto intro: supports_finite simp add: finite_supp)
  have "supp (bs, y, c) supports (f bs y c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm2 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin2: "finite (supp (f bs y c))"
    by (auto intro: supports_finite simp add: finite_supp)
  obtain q::"perm" where 
    fr1: "(q \<bullet> (set as)) \<sharp>* (x, c, f as x c, f bs y c)" and 
    fr2: "supp q \<sharp>* Abs_lst as x" and 
    inc: "supp q \<subseteq> (set as) \<union> q \<bullet> (set as)"
    using at_set_avoiding3[where xs="set as" and c="(x, c, f as x c, f bs y c)" and x="[as]lst. x"]  
      fin1 fin2
    by (auto simp add: supp_Pair finite_supp Abs_fresh_star dest: fresh_star_supp_conv)
  have "Abs_lst (q \<bullet> as) (q \<bullet> x) = q \<bullet> Abs_lst as x" by simp
  also have "\<dots> = Abs_lst as x"
    by (simp only: fr2 perm_supp_eq)
  finally have "Abs_lst (q \<bullet> as) (q \<bullet> x) = Abs_lst bs y" using eq by simp
  then obtain r::perm where 
    qq1: "q \<bullet> x = r \<bullet> y" and 
    qq2: "q \<bullet> as = r \<bullet> bs" and 
    qq3: "supp r \<subseteq> (q \<bullet> (set as)) \<union> set bs"
    apply(drule_tac sym)
    apply(simp only: Abs_eq_iff2 alphas)
    apply(erule exE)
    apply(erule conjE)+
    apply(drule_tac x="p" in meta_spec)
    apply(simp add: set_eqvt)
    apply(blast)
    done
  have "(set as) \<sharp>* f as x c" 
    apply(rule fcb1)
    apply(rule fresh1)
    done
  then have "q \<bullet> ((set as) \<sharp>* f as x c)"
    by (simp add: permute_bool_def)
  then have "set (q \<bullet> as) \<sharp>* f (q \<bullet> as) (q \<bullet> x) c"
    apply(simp add: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm1)
    using inc fresh1 fr1
    apply(auto simp add: fresh_star_def fresh_Pair)
    done
  then have "set (r \<bullet> bs) \<sharp>* f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  then have "r \<bullet> ((set bs) \<sharp>* f bs y c)"
    apply(simp add: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm2[symmetric])
    using qq3 fresh2 fr1
    apply(auto simp add: set_eqvt fresh_star_def fresh_Pair)
    done
  then have fcb2: "(set bs) \<sharp>* f bs y c" by (simp add: permute_bool_def)
  have "f as x c = q \<bullet> (f as x c)"
    apply(rule perm_supp_eq[symmetric])
    using inc fcb1[OF fresh1] fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (q \<bullet> as) (q \<bullet> x) c" 
    apply(rule perm1)
    using inc fresh1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  also have "\<dots> = r \<bullet> (f bs y c)"
    apply(rule perm2[symmetric])
    using qq3 fresh2 fr1 by (auto simp add: fresh_star_def)
  also have "... = f bs y c"
    apply(rule perm_supp_eq)
    using qq3 fr1 fcb2 by (auto simp add: fresh_star_def)
  finally show ?thesis by simp
qed

lemma Abs_lst1_fcb2:
  fixes a b :: "atom"
    and x y :: "'b :: fs"
    and c::"'c :: fs"
  assumes e: "(Abs_lst [a] x) = (Abs_lst [b] y)"
  and fcb1: "a \<sharp> c \<Longrightarrow> a \<sharp> f a x c"
  and fresh: "{a, b} \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f a x c) = f (p \<bullet> a) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f b y c) = f (p \<bullet> b) (p \<bullet> y) c"
  shows "f a x c = f b y c"
using e
apply(drule_tac Abs_lst_fcb2[where c="c" and f="\<lambda>(as::atom list) . f (hd as)"])
apply(simp_all)
using fcb1 fresh perm1 perm2
apply(simp_all add: fresh_star_def)
done


function
  apply_assn2 :: "(trm \<Rightarrow> trm) \<Rightarrow> assn \<Rightarrow> assn"
where
  "apply_assn2 f ANil = ANil"
| "apply_assn2 f (ACons x t as) = ACons x (f t) (apply_assn2 f as)"
  apply(case_tac x)
  apply(case_tac b rule: trm_assn.exhaust(2))
  apply(simp_all)
  apply(blast)
  done

termination by lexicographic_order

lemma apply_assn_eqvt[eqvt]:
  "p \<bullet> (apply_assn2 f a) = apply_assn2 (p \<bullet> f) (p \<bullet> a)"
  apply(induct f a rule: apply_assn2.induct)
  apply simp_all
  apply(perm_simp)
  apply rule
  done

lemma
  fixes x y :: "'a :: fs"
  shows "[a # as]lst. x = [b # bs]lst. y \<Longrightarrow> [[a]]lst. [as]lst. x = [[b]]lst. [bs]lst. y"
  apply (simp add: Abs_eq_iff)
  apply (elim exE)
  apply (rule_tac x="p" in exI)
  apply (simp add: alphas)
  apply clarify
  apply rule
  apply (simp add: supp_Abs)
  apply blast
  apply (simp add: supp_Abs fresh_star_def)
  apply blast
  done

lemma
  assumes neq: "a \<noteq> b" "sort_of a = sort_of b"
  shows "[[a]]lst. [[a]]lst. a = [[a]]lst. [[b]]lst. b \<and> [[a, a]]lst. a \<noteq> [[a, b]]lst. b"
  apply (simp add: Abs1_eq_iff)
  apply rule
  apply (simp add: Abs_eq_iff alphas supp_atom fresh_star_def)
  apply (rule_tac x="(a \<rightleftharpoons> b)" in exI)
  apply (simp add: neq)
  apply (simp add: Abs_eq_iff alphas supp_atom fresh_star_def neq)
  done

nominal_function
    subst  :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
where
  "subst s t (Var x) = (if (s = x) then t else (Var x))"
| "subst s t (App l r) = App (subst s t l) (subst s t r)"
| "atom v \<sharp> (s, t) \<Longrightarrow> subst s t (Lam v b) = Lam v (subst s t b)"
| "set (bn as) \<sharp>* (s, t) \<Longrightarrow> subst s t (Let as b) = Let (apply_assn2 (subst s t) as) (subst s t b)"
  apply (simp only: eqvt_def subst_graph_def)
  apply (rule, perm_simp, rule)
  apply (rule TrueI)
  apply (case_tac x)
  apply (rule_tac y="c" and c="(a,b)" in trm_assn.strong_exhaust(1))
  apply (auto simp add: fresh_star_def)[3]
  apply (drule_tac x="assn" in meta_spec)
  apply (simp add: Abs1_eq_iff alpha_bn_refl)
  apply auto[7]
  prefer 2
  apply(simp)
  thm subst_sumC_def
  thm THE_default_def
  thm theI
  apply (erule_tac c="(sa, ta)" in Abs_lst1_fcb2)
  apply (simp add: Abs_fresh_iff)
  apply (simp add: fresh_star_def)
  apply (simp_all add: fresh_star_Pair_elim perm_supp_eq eqvt_at_def)[2]
  apply (subgoal_tac "apply_assn2 (\<lambda>x2\<Colon>trm. subst_sumC (sa, ta, x2)) asa
    = apply_assn2 (\<lambda>x2\<Colon>trm. subst_sumC (sa, ta, x2)) as")
  prefer 2
  apply (erule alpha_bn_inducts)
  apply simp
  apply (simp only: apply_assn2.simps)
  apply simp
--"We know nothing about names; not true; but we can apply fcb2"
  defer
  apply (simp only: )
  apply (erule_tac c="(sa, ta)" in Abs_lst_fcb2)
--"We again need induction for fcb assumption; this time true"
  apply (induct_tac as rule: trm_assn.inducts(2))
  apply (rule TrueI)+
  apply (simp_all add: trm_assn.bn_defs fresh_star_def)[2]
  apply (auto simp add: Abs_fresh_iff)[1]
  apply assumption+
--"But eqvt is not going to be true as well"
  apply (simp add: fresh_star_Pair_elim perm_supp_eq eqvt_at_def trm_assn.fv_bn_eqvt)
  apply (simp add: apply_assn_eqvt)
  apply (drule sym)
  apply (subgoal_tac "p \<bullet> (\<lambda>x2\<Colon>trm. subst_sumC (sa, ta, x2)) = (\<lambda>x2\<Colon>trm. subst_sumC (sa, ta, x2))")
  apply (simp)
  apply (erule alpha_bn_inducts)
  apply simp
  apply simp
  apply (simp add: trm_assn.bn_defs)
--"Again we cannot relate 'namea' with 'p \<bullet> name'"
  prefer 4
  apply (erule alpha_bn_inducts)
  apply simp_all[2]
  oops

end
