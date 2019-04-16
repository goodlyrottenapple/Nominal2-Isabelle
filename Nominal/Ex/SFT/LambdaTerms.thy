header {* Definition of Lambda terms and convertibility *}

theory LambdaTerms imports "../../Nominal2" begin

lemma [simp]: "supp x = {} \<Longrightarrow> y \<sharp> x"
  unfolding fresh_def by blast

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

notation
  App (infixl "\<cdot>" 98) and
  Lam ("\<integral> _. _" [97, 97] 99)

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(t1 \<cdot> t2)[y ::= s] = (t1[y ::= s]) \<cdot> (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (\<integral>x. t)[y ::= s] = \<integral>x.(t[y ::= s])"
proof auto
  fix a b :: lam and aa :: name and P
  assume "\<And>x y s. a = Var x \<and> aa = y \<and> b = s \<Longrightarrow> P"
    "\<And>t1 t2 y s. a = t1 \<cdot> t2 \<and> aa = y \<and> b = s \<Longrightarrow> P"
    "\<And>x y s t. \<lbrakk>atom x \<sharp> (y, s); a = \<integral> x. t \<and> aa = y \<and> b = s\<rbrakk> \<Longrightarrow> P"
  then show "P"
    by (rule_tac y="a" and c="(aa, b)" in lam.strong_exhaust)
       (blast, blast, simp add: fresh_star_def)
next
  fix x :: name and t and xa :: name and ya sa ta
  assume *: "eqvt_at subst_sumC (t, ya, sa)"
    "atom x \<sharp> (ya, sa)" "atom xa \<sharp> (ya, sa)"
    "[[atom x]]lst. t = [[atom xa]]lst. ta"
  then show "[[atom x]]lst. subst_sumC (t, ya, sa) = [[atom xa]]lst. subst_sumC (ta, ya, sa)"
    apply -
    apply (erule Abs_lst1_fcb)
    apply(simp (no_asm) add: Abs_fresh_iff)
    apply(drule_tac a="atom xa" in fresh_eqvt_at)
    apply(simp add: finite_supp)
    apply(simp_all add: fresh_Pair_elim Abs_fresh_iff Abs1_eq_iff)
    apply(subgoal_tac "(atom x \<rightleftharpoons> atom xa) \<bullet> ya = ya")
    apply(subgoal_tac "(atom x \<rightleftharpoons> atom xa) \<bullet> sa = sa")
    apply(simp add: atom_eqvt eqvt_at_def)
    apply(rule perm_supp_eq, simp add: supp_swap fresh_star_def fresh_Pair)+
    done
next
  show "eqvt subst_graph" unfolding eqvt_def subst_graph_def
    by (rule, perm_simp, rule)
qed

nominal_termination (eqvt) by lexicographic_order

lemma forget[simp]:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma forget_closed[simp]: "supp t = {} \<Longrightarrow> t[x ::= s] = t"
  by (simp add: fresh_def)

lemma subst_id[simp]: "M [x ::= Var x] = M"
  by (rule_tac lam="M" and c="x" in lam.strong_induct)
     (simp_all add: fresh_star_def lam.fresh fresh_Pair)

inductive
  beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (infix "\<approx>" 80)
where
  bI: "(\<integral>x. M) \<cdot> N \<approx> M[x ::= N]"
| b1: "M \<approx> M"
| b2: "M \<approx> N \<Longrightarrow> N \<approx> M"
| b3: "M \<approx> N \<Longrightarrow> N \<approx> L \<Longrightarrow> M \<approx> L"
| b4: "M \<approx> N \<Longrightarrow> Z \<cdot> M \<approx> Z \<cdot> N"
| b5: "M \<approx> N \<Longrightarrow> M \<cdot> Z \<approx> N \<cdot> Z"
| b6: "M \<approx> N \<Longrightarrow> \<integral>x. M \<approx> \<integral>x. N"

lemmas [trans] = b3
equivariance beta

end
