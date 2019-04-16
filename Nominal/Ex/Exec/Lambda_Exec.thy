theory Lambda_Exec
imports Name_Exec
begin

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
proof auto
  fix a b :: lam and aa :: name and P
  assume "\<And>x y s. a = Var x \<and> aa = y \<and> b = s \<Longrightarrow> P"
    "\<And>t1 t2 y s. a = App t1 t2 \<and> aa = y \<and> b = s \<Longrightarrow> P"
    "\<And>x y s t. \<lbrakk>atom x \<sharp> (y, s); a = Lam [x]. t \<and> aa = y \<and> b = s\<rbrakk> \<Longrightarrow> P"
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

termination (eqvt) by lexicographic_order

datatype ln =
  LNBnd nat
| LNVar name
| LNApp ln ln
| LNLam ln

instantiation ln :: pt begin
fun
  permute_ln
where
  "p \<bullet> LNBnd n = LNBnd (p \<bullet> n)"
| "p \<bullet> LNVar v = LNVar (p \<bullet> v)"
| "p \<bullet> LNApp d1 d2 = LNApp (p \<bullet> d1) (p \<bullet> d2)"
| "p \<bullet> LNLam d = LNLam (p \<bullet> d)"
instance
  by (default, induct_tac [!] x) simp_all
end

lemmas [eqvt] = permute_ln.simps

lemma ln_supports:
  "supp (n) supports LNBnd n"
  "supp (v) supports LNVar v"
  "supp (za, z) supports LNApp z za"
  "supp (z) supports LNLam z"
  by (simp_all add: supports_def fresh_def[symmetric])
     (perm_simp, simp add: swap_fresh_fresh fresh_Pair)+

instance ln :: fs
  apply default
  apply (induct_tac x)
  apply (rule supports_finite, rule ln_supports, simp add: finite_supp supp_Pair)+
  done

lemma ln_supp:
  "supp (LNBnd n) = supp n"
  "supp (LNVar name) = supp name"
  "supp (LNApp ln1 ln2) = supp ln1 \<union> supp ln2"
  "supp (LNLam ln) = supp ln"
  unfolding supp_Pair[symmetric]
  by (simp_all add: supp_def)

lemma ln_fresh:
  "x \<sharp> LNBnd n \<longleftrightarrow> True"
  "x \<sharp> LNVar name \<longleftrightarrow> x \<sharp> name"
  "x \<sharp> LNApp ln1 ln2 \<longleftrightarrow> x \<sharp> ln1 \<and> x \<sharp> ln2"
  "x \<sharp> LNLam ln = x \<sharp> ln"
  unfolding fresh_def
  by (simp_all add: ln_supp pure_supp)

fun
  lookup :: "name list \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> ln"
where
  "lookup [] n x = LNVar x"
| "lookup (y # ys) n x = (if x = y then LNBnd n else (lookup ys (n + 1) x))"

lemma supp_lookup:
  shows "supp (lookup xs n x) \<subseteq> {atom x}"
  by (induct arbitrary: n rule: lookup.induct)
     (simp_all add: supp_at_base ln_supp pure_supp)

lemma supp_lookup_in:
  shows "x \<in> set xs \<Longrightarrow> supp (lookup xs n x) = {}"
  by (induct arbitrary: n rule: lookup.induct) (auto simp add: ln_supp pure_supp)

lemma supp_lookup_notin:
  shows "x \<notin> set xs \<Longrightarrow> supp (lookup xs n x) = {atom x}"
  by (induct arbitrary: n rule: lookup.induct) (auto simp add: ln_supp pure_supp supp_at_base)

lemma supp_lookup_fresh:
  shows "atom ` set xs \<sharp>* lookup xs n x"
  by (case_tac "x \<in> set xs") (auto simp add: fresh_star_def fresh_def supp_lookup_in supp_lookup_notin)

lemma lookup_eqvt[eqvt]:
  shows "(p \<bullet> lookup xs n x) = lookup (p \<bullet> xs) (p \<bullet> n) (p \<bullet> x)"
  by (induct xs arbitrary: n) (simp_all add: permute_pure)

nominal_function (invariant "\<lambda>(_, xs) y. atom ` set xs \<sharp>* y")
  lam_ln_aux :: "lam \<Rightarrow> name list \<Rightarrow> ln"
where
  "lam_ln_aux (Var x) xs = lookup xs 0 x"
| "lam_ln_aux (App t1 t2) xs = LNApp (lam_ln_aux t1 xs) (lam_ln_aux t2 xs)"
| "atom x \<sharp> xs \<Longrightarrow> lam_ln_aux (Lam [x]. t) xs = LNLam (lam_ln_aux t (x # xs))"
  apply (simp add: eqvt_def lam_ln_aux_graph_def)
  apply (rule, perm_simp, rule)
  apply (erule lam_ln_aux_graph.induct)
  apply (auto simp add: ln_supp)[3]
  apply (simp add: supp_lookup_fresh)
  apply (simp add: fresh_star_def ln_supp fresh_def)
  apply (simp add: ln_supp fresh_def fresh_star_def)
  apply (case_tac x)
  apply (rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply (auto simp add: fresh_star_def)[3]
  apply(simp_all)
  apply(erule conjE)
  apply (erule_tac c="xsa" in Abs_lst1_fcb2')
  apply (simp_all add: fresh_star_def)[2]
  apply (simp_all add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  done

termination (eqvt) by lexicographic_order

definition lam_ln where "lam_ln t \<equiv> lam_ln_aux t []"

fun nth_or_def where
  "nth_or_def [] _ d = d"
| "nth_or_def (h # t) 0 d = h"
| "nth_or_def (h # t) (Suc n) d = nth_or_def t n d"

lemma nth_or_def_eqvt [eqvt]:
  "p \<bullet> (nth_or_def l n d) = nth_or_def (p \<bullet> l) (p \<bullet> n) (p \<bullet> d)"
  apply (cases l)
  apply auto
  apply (induct n arbitrary: list)
  apply (auto simp add: permute_pure)
  apply (case_tac list)
  apply simp_all
  done

nominal_function
  ln_lam_aux :: "ln \<Rightarrow> name list \<Rightarrow> lam"
where
  "ln_lam_aux (LNBnd n) ns = (nth_or_def (map Var ns) n (Lam [x]. Var x))"
| "ln_lam_aux (LNVar v) ns = Var v"
| "ln_lam_aux (LNApp l1 l2) ns = App (ln_lam_aux l1 ns) (ln_lam_aux l2 ns)"
| "atom x \<sharp> (ns, l) \<Longrightarrow> ln_lam_aux (LNLam l) ns = Lam [x]. (ln_lam_aux l (x # ns))"
  apply (simp add: eqvt_def ln_lam_aux_graph_def)
  apply (rule, perm_simp, rule)
  apply rule
  apply(auto)[1]
  apply (rule_tac y="a" in ln.exhaust)
  apply (auto simp add: fresh_star_def)[4]
  using obtain_fresh apply metis
  apply (auto simp add: fresh_Pair_elim)
  apply (subgoal_tac "Lam [x]. Var x = Lam [xa]. Var xa")
  apply (simp del: lam.eq_iff)
  apply (simp add: Abs1_eq_iff lam.fresh fresh_at_base)
  apply (simp add: Abs1_eq_iff)
  apply (case_tac "x=xa")
  apply simp_all
  apply rule
  apply (auto simp add: eqvt_at_def swap_fresh_fresh)[1]
  apply (erule fresh_eqvt_at)
  apply (simp add: supp_Pair finite_supp)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base)
  done

termination (eqvt)
  by lexicographic_order

definition ln_lam where "ln_lam t \<equiv> ln_lam_aux t []"

lemma l_fresh_lam_ln_aux: "atom ` set l \<sharp>* lam_ln_aux t l"
  apply (nominal_induct t avoiding: l rule: lam.strong_induct)
  apply (simp_all add: fresh_def ln_supp pure_supp)
  apply (auto simp add: fresh_star_def)[1]
  apply (case_tac "a = name")
  apply (auto simp add: supp_lookup_in fresh_def)[1]
  apply (simp add: fresh_def)
  using supp_lookup
  apply (metis (lifting) atom_eq_iff equals0D singletonE supp_lookup_in supp_lookup_notin)
  apply (simp add: fresh_star_def fresh_def ln_supp)+
  done

lemma supp_lam_ln_aux: "supp (lam_ln_aux t l) \<subseteq> supp t"
proof -
  have "eqvt lam_ln_aux" unfolding eqvt_def using eqvts_raw by simp
  then have "supp lam_ln_aux = {}" using supp_fun_eqvt by auto
  then have "supp (lam_ln_aux t) \<subseteq> supp t" using supp_fun_app by auto
  then have "supp (lam_ln_aux t l) \<subseteq> supp t \<union> supp l" using supp_fun_app by auto
  moreover have "\<forall>x \<in> supp l. x \<notin> supp (lam_ln_aux t l)"
    using l_fresh_lam_ln_aux unfolding fresh_star_def fresh_def
    by (metis finite_set supp_finite_set_at_base supp_set)
  ultimately show "supp (lam_ln_aux t l) \<subseteq> supp t" by blast
qed

lemma lookup_flip: "x \<noteq> y \<Longrightarrow> y \<noteq> a \<Longrightarrow> lookup ((x \<leftrightarrow> a) \<bullet> xs) n y = lookup xs n y"
  apply (induct xs arbitrary: n)
  apply simp
  apply (simp only: Cons_eqvt)
  apply (simp only: lookup.simps)
  apply (subgoal_tac "y = (x \<leftrightarrow> a) \<bullet> aa \<longleftrightarrow> y = aa")
  apply simp
  by (metis permute_flip_at)

lemma lookup_append_flip: "x \<noteq> y \<Longrightarrow> lookup (l @ a # (x \<leftrightarrow> a) \<bullet> xs) n y = lookup (l @ a # xs) n y"
  by (induct l arbitrary: n) (auto simp add: lookup_flip)

lemma lam_ln_aux_flip: "atom x \<sharp> t \<Longrightarrow> lam_ln_aux t (l @ a # (x \<leftrightarrow> a) \<bullet> xs) = lam_ln_aux t (l @ a # xs)"
  apply (nominal_induct t avoiding: x a xs l rule: lam.strong_induct)
  apply (simp_all add: lam_ln_aux.eqvt lam.fresh lookup_append_flip fresh_at_base)[2]
  apply (simp add: lam.fresh fresh_at_base)
  apply (subst lam_ln_aux.simps)
  apply (simp add: fresh_Cons fresh_at_base fresh_append)
  apply (metis atom_eqvt atom_name_def flip_at_base_simps(3) flip_commute fresh_permute_iff)
  apply (subst lam_ln_aux.simps)
  apply (simp add: fresh_Cons fresh_at_base fresh_append)
  apply simp
  apply (drule_tac x="x" in meta_spec)
  apply (drule_tac x="a" in meta_spec)
  apply (drule_tac x="xs" in meta_spec)
  apply (drule_tac x="name # l" in meta_spec)
  apply simp
  done

lemma lam_ln_aux4: "lam_ln_aux (Lam [x]. t) xs = LNLam (lam_ln_aux t (x # xs))"
  apply (rule_tac 'a="name" and x="(xs, x, t)" in obtain_fresh)
  apply (simp add: fresh_Pair_elim)
  apply (rule_tac t="Lam [x]. t" and s="Lam [a]. ((x \<leftrightarrow> a) \<bullet> t)" in subst)
  apply (auto simp add: Abs1_eq_iff lam.fresh flip_def swap_commute)[1]
  apply simp
  apply (rule_tac s="(x \<leftrightarrow> a) \<bullet> lam_ln_aux t (x # xs)" in trans)
  apply (simp add: lam_ln_aux.eqvt)
  apply (subst lam_ln_aux_flip[of _ _ "[]", simplified])
  apply (metis atom_eqvt flip_at_simps(2) fresh_permute_iff)
  apply rule
  apply (rule flip_fresh_fresh)
  apply (simp add: l_fresh_lam_ln_aux[of "x # xs", simplified fresh_star_def, simplified])
  apply (simp add: fresh_def)
  apply (metis set_rev_mp supp_lam_ln_aux)
  done

lemma lookup_in: "n \<notin> set l \<Longrightarrow> lookup l i n = LNVar n"
  by (induct l arbitrary: i n) simp_all

lemma lookup_in2: "n \<in> set l \<Longrightarrow> \<exists>i. lookup l j n = LNBnd i"
  by (induct l arbitrary: j n) auto

lemma lookup_in2': "lookup l j n = LNBnd i \<Longrightarrow> lookup l (Suc j) n = LNBnd (Suc i)"
  by (induct l arbitrary: j n) auto

lemma ln_lam_Var: "ln_lam_aux (lookup l (0\<Colon>nat) n) l = Var n"
  apply (cases "n \<in> set l")
  apply (simp_all add: lookup_in)
  apply (induct l arbitrary: n)
  apply simp
  apply (case_tac "a = n")
  apply (simp_all add: ln_lam_aux.simps(1)[of _ _ "Name 0"] )[2]
  apply (drule_tac x="n" in meta_spec)
  apply (frule lookup_in2[of _ _ 0])
  apply (erule exE)
  apply simp
  apply (frule lookup_in2')
  apply simp
  apply (simp_all add: ln_lam_aux.simps(1)[of _ _ "Name 0"] )
  done

lemma ln_lam_ln_aux: "ln_lam_aux (lam_ln_aux t l) l = t"
  apply (nominal_induct t avoiding: l rule: lam.strong_induct)
  apply (simp_all add: ln_lam_Var)
  apply (subst ln_lam_aux.simps(4)[of name])
  apply (simp add: fresh_Pair)
  apply (subgoal_tac "atom ` set (name # l) \<sharp>* lam_ln_aux lam (name # l)")
  apply (simp add: fresh_star_def)
  apply (rule l_fresh_lam_ln_aux)
  apply simp
  done

fun subst_ln_nat where
  "subst_ln_nat (LNBnd n) x _ = LNBnd n"
| "subst_ln_nat (LNVar v) x n = (if x = v then LNBnd n else LNVar v)"
| "subst_ln_nat (LNApp l r) x n = LNApp (subst_ln_nat l x n) (subst_ln_nat r x n)"
| "subst_ln_nat (LNLam l) x n = LNLam (subst_ln_nat l x (n + 1))"

lemma subst_ln_nat_eqvt[eqvt]:
  shows "(p \<bullet> subst_ln_nat t x n) = subst_ln_nat (p \<bullet> t) (p \<bullet> x) (p \<bullet> n)"
  by (induct t arbitrary: n) (simp_all add: permute_pure)

lemma supp_subst_ln_nat:
  "supp (subst_ln_nat t x n) = supp t - {atom x}"
  by (induct t arbitrary: n) (auto simp add: permute_pure ln_supp pure_supp supp_at_base)

lemma fresh_subst_ln_nat:
  "atom y \<sharp> subst_ln_nat t x n \<longleftrightarrow> y = x \<or> atom y \<sharp> t"
  unfolding fresh_def supp_subst_ln_nat by auto

nominal_function
  lam_ln_ex :: "lam \<Rightarrow> ln"
where
  "lam_ln_ex (Var x) = LNVar x"
| "lam_ln_ex (App t1 t2) = LNApp (lam_ln_ex t1) (lam_ln_ex t2)"
| "lam_ln_ex (Lam [x]. t) = LNLam (subst_ln_nat (lam_ln_ex t) x 0)"
  apply (simp add: eqvt_def lam_ln_ex_graph_def)
  apply (rule, perm_simp, rule)
  apply rule
  apply (rule_tac y="x" in lam.exhaust)
  apply (auto simp add: fresh_star_def)[3]
  apply(simp_all)
  apply (erule_tac Abs_lst1_fcb)
  apply (simp add: fresh_subst_ln_nat)
  apply (simp add: fresh_subst_ln_nat)
  apply (erule fresh_eqvt_at)
  apply (simp add: finite_supp)
  apply assumption
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq
    subst_ln_nat_eqvt permute_pure)
  apply simp
  done

termination (eqvt) by lexicographic_order

lemma lookup_in3: "lookup l j n = LNBnd i \<Longrightarrow> lookup (l @ l2) j n = LNBnd i"
  by (induct l arbitrary: j n) auto

lemma lookup_in4: "n \<notin> set l \<Longrightarrow> lookup (l @ [n]) j n = LNBnd (length l + j)"
  by (induct l arbitrary: j n) auto

lemma subst_ln_nat_lam_ln_aux: "subst_ln_nat (lam_ln_aux l ns) n (List.length ns) = lam_ln_aux l (ns @ [n])"
  apply (nominal_induct l avoiding: n ns rule: lam.strong_induct)
  apply simp defer
  apply simp
  apply (simp add: fresh_Nil fresh_Cons fresh_append)
  apply (drule_tac x="n" in meta_spec)
  apply (drule_tac x="name # ns" in meta_spec)
  apply simp
  apply (case_tac "name \<in> set ns")
  apply (simp_all add: lookup_in)
  apply (frule lookup_in2[of _ _ 0])
  apply (erule exE)
  apply (simp add: lookup_in3)
  apply (simp add: lookup_in4)
  done

lemma lam_ln_ex: "lam_ln_ex t = lam_ln t"
  apply (induct t rule: lam.induct)
  apply (simp_all add: lam_ln_def fresh_Nil)
  by (metis (lifting) list.size(3) self_append_conv2 subst_ln_nat_lam_ln_aux)

(* Lambda terms as a code-abstype *)
lemma ln_abstype[code abstype]:
  "ln_lam (lam_ln_ex t) = t"
  by (simp add: ln_lam_def lam_ln_ex lam_ln_def ln_lam_ln_aux)

lemmas [code abstract] = lam_ln_ex.simps

(* Equality for lambda-terms *)
instantiation lam :: equal begin

definition equal_lam_def: "equal_lam a b \<longleftrightarrow> lam_ln_ex a = lam_ln_ex b"

instance
  by default
    (metis equal_lam_def lam_ln_def lam_ln_ex ln_lam_ln_aux)

end

(* Execute permutations *)
lemmas [code abstract] = lam_ln_ex.eqvt[symmetric]

fun subst_ln where
  "subst_ln (LNBnd n) _ _ = LNBnd n"
| "subst_ln (LNVar v) x t = (if x = v then t else LNVar v)"
| "subst_ln (LNApp l r) x t = LNApp (subst_ln l x t) (subst_ln r x t)"
| "subst_ln (LNLam l) x t = LNLam (subst_ln l x t)"

lemma subst_ln_nat_id[simp]:
  "atom name \<sharp> s \<Longrightarrow> name \<noteq> y \<Longrightarrow> subst_ln_nat s name n = s"
  by (induct s arbitrary: n) (simp_all add: ln_fresh fresh_at_base)

lemma subst_ln_nat_subst_ln_commute:
  assumes "name \<noteq> y" and "atom name \<sharp> s"
  shows "subst_ln_nat (subst_ln ln y s) name n = subst_ln (subst_ln_nat ln name n) y s"
  using assms by (induct ln arbitrary: n) auto

lemma supp_lam_ln_ex: "supp (lam_ln_ex t) = supp t"
  by (induct t rule: lam.induct) (simp_all add: lam.supp ln_supp supp_subst_ln_nat)

lemma subst_code[code abstract]:
  "lam_ln_ex (subst t y s) = subst_ln (lam_ln_ex t) y (lam_ln_ex s)"
  apply (nominal_induct t avoiding: y s rule: lam.strong_induct)
  apply simp_all
  apply (subst subst_ln_nat_subst_ln_commute)
  apply (simp_all add: fresh_at_base supp_lam_ln_ex fresh_def)
  done

(*definition "I0 \<equiv> Lam [N0]. (Var N0)"
definition "I1 \<equiv> Lam [N1]. (Var N1)"
definition "ppp = (atom N0 \<rightleftharpoons> atom N1)"
definition "pp \<equiv> ppp \<bullet> I1 = I0"

export_code pp in SML*)

lemma subst_ln_nat_funpow[simp]:
  "subst_ln_nat ((LNLam^^p) l) x n = (LNLam ^^ p) (subst_ln_nat l x (n + p))"
  by (induct p arbitrary: n) simp_all

(*

Tests:

fun Umn :: "nat \<Rightarrow> nat \<Rightarrow> lam"
where
  "Umn 0 n = Lam [Name 0]. Var (Name n)"
| "Umn (Suc m) n = Lam [Name (Suc m)]. Umn m n"

lemma Umn_faster:
  "lam_ln_ex (Umn m n) = (LNLam ^^ (Suc m)) (if n \<le> m then LNBnd n else LNVar (Name n))"
  apply (induct m)
  apply (auto simp add: Umn.simps)
  apply (simp_all add: Name_def Abs_name_inject le_SucE)
  apply (erule le_SucE)
  apply simp_all
  done

definition "Bla = Umn 2 2"

definition vara where "vara \<equiv> Lam [N0]. Lam [N1]. (App (Var N1) (App (Umn 2 2) (App (Var N0) (Var N1))))"

export_code ln_lam_aux nth_or_def ln_lam subst vara in SML

value "(atom N0 \<rightleftharpoons> atom N1) \<bullet> (App (Var N0) (Lam [N1]. (Var N1)))"
value "subst ((N0 \<leftrightarrow> N1) \<bullet> (App (Var N0) (Lam [N1]. (Var N1)))) N1 (Var N0)"*)

end



