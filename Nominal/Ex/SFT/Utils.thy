header {* Utilities for defining constants and functions *}

theory Utils imports LambdaTerms begin

lemma beta_app:
  "(\<integral> x. M) \<cdot> Var x \<approx> M"
  by (rule b3, rule bI)
     (simp add: b1)

lemma lam1_fast_app:
  assumes leq: "\<And>a. (L = \<integral> a. (F (V a)))"
      and su: "\<And>x. atom x \<sharp> A \<Longrightarrow> F (V x) [x ::= A] = F A"
  shows "L \<cdot> A \<approx> F A"
proof -
  obtain x :: name where a: "atom x \<sharp> A" using obtain_fresh by blast
  show ?thesis
    by (simp add: leq[of x], rule b3, rule bI, simp add: su b1 a)
qed

lemma lam2_fast_app:
  assumes leq: "\<And>a b. a \<noteq> b \<Longrightarrow> L = \<integral> a. \<integral> b. (F (V a) (V b))"
     and su: "\<And>x y. atom x \<sharp> A \<Longrightarrow> atom y \<sharp> A \<Longrightarrow> atom x \<sharp> B \<Longrightarrow> atom y \<sharp> B \<Longrightarrow>
       x \<noteq> y \<Longrightarrow> F (V x) (V y) [x ::= A] [y ::= B] = F A B"
  shows "L \<cdot> A \<cdot> B \<approx> F A B"
proof -
  obtain x :: name where a: "atom x \<sharp> (A, B)" using obtain_fresh by blast
  obtain y :: name where b: "atom y \<sharp> (x, A, B)" using obtain_fresh by blast
  obtain z :: name where c: "atom z \<sharp> (x, y, A, B)" using obtain_fresh by blast
  have *: "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    using a b c by (simp_all add: fresh_Pair fresh_at_base) blast+
  have ** : "atom y \<sharp> z" "atom x \<sharp> z" "atom y \<sharp> x"
            "atom z \<sharp> y" "atom z \<sharp> x" "atom x \<sharp> y"
            "atom x \<sharp> A" "atom y \<sharp> A" "atom z \<sharp> A"
            "atom x \<sharp> B" "atom y \<sharp> B" "atom z \<sharp> B"
    using a b c by (simp_all add: fresh_Pair fresh_at_base) blast+
  show ?thesis
    apply (simp add: leq[OF *(1)])
    apply (rule b3) apply (rule b5) apply (rule bI)
    apply (simp add: ** fresh_Pair)
    apply (rule b3) apply (rule bI) apply (simp add: su b1 ** *)
    done
  qed

lemma lam3_fast_app:
  assumes leq: "\<And>a b c. a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> c \<noteq> a \<Longrightarrow>
       L = \<integral> a. \<integral> b. \<integral> c. (F (V a) (V b) (V c))"
     and su: "\<And>x y z. atom x \<sharp> A \<Longrightarrow> atom y \<sharp> A \<Longrightarrow> atom z \<sharp> A \<Longrightarrow>
                     atom x \<sharp> B \<Longrightarrow> atom y \<sharp> B \<Longrightarrow> atom z \<sharp> B \<Longrightarrow>
                     atom y \<sharp> B \<Longrightarrow> atom y \<sharp> B \<Longrightarrow> atom z \<sharp> B \<Longrightarrow>
                     x \<noteq> y \<Longrightarrow> y \<noteq> z \<Longrightarrow> z \<noteq> x \<Longrightarrow>
      ((F (V x) (V y) (V z))[x ::= A] [y ::= B] [z ::= C] = F A B C)"
  shows "L \<cdot> A \<cdot> B \<cdot> C \<approx> F A B C"
proof -
  obtain x :: name where a: "atom x \<sharp> (A, B, C)" using obtain_fresh by blast
  obtain y :: name where b: "atom y \<sharp> (x, A, B, C)" using obtain_fresh by blast
  obtain z :: name where c: "atom z \<sharp> (x, y, A, B, C)" using obtain_fresh by blast
  have *: "x \<noteq> y" "y \<noteq> z" "z \<noteq> x"
    using a b c by (simp_all add: fresh_Pair fresh_at_base) blast+
  have ** : "atom y \<sharp> z" "atom x \<sharp> z" "atom y \<sharp> x"
            "atom z \<sharp> y" "atom z \<sharp> x" "atom x \<sharp> y"
            "atom x \<sharp> A" "atom y \<sharp> A" "atom z \<sharp> A"
            "atom x \<sharp> B" "atom y \<sharp> B" "atom z \<sharp> B"
            "atom x \<sharp> C" "atom y \<sharp> C" "atom z \<sharp> C"
    using a b c by (simp_all add: fresh_Pair fresh_at_base) blast+
  show ?thesis
    apply (simp add: leq[OF *(1) *(2) *(3)])
    apply (rule b3) apply (rule b5) apply (rule b5) apply (rule bI)
    apply (simp add: ** fresh_Pair)
    apply (rule b3) apply (rule b5) apply (rule bI)
    apply (simp add: ** fresh_Pair)
    apply (rule b3) apply (rule bI) apply (simp add: su b1 ** *)
    done
  qed

definition cn :: "nat \<Rightarrow> name" where "cn n \<equiv> Abs_name (Atom (Sort ''LambdaTerms.name'' []) n)"

lemma cnd[simp]: "m \<noteq> n \<Longrightarrow> cn m \<noteq> cn n"
  unfolding cn_def using Abs_name_inject by simp

definition cx :: name where "cx \<equiv> cn 0"
definition cy :: name where "cy \<equiv> cn 1"
definition cz :: name where "cz \<equiv> cn 2"

lemma cx_cy_cz[simp]:
  "cx \<noteq> cy" "cx \<noteq> cz" "cz \<noteq> cy"
  unfolding cx_def cy_def cz_def
  by simp_all

lemma noteq_fresh: "atom x \<sharp> y = (x \<noteq> y)"
  by (simp add: fresh_at_base(2))

lemma fresh_fun_eqvt_app2:
  assumes a: "eqvt f"
  and b: "a \<sharp> x" "a \<sharp> y"
  shows "a \<sharp> f x y"
  using fresh_fun_eqvt_app[OF a b(1)] a b
  by (metis fresh_fun_app)

end



