header {* The main lemma about NUM and the Second Fixed Point Theorem *}

theory Theorem imports Consts begin

lemmas [simp] = b3[OF bI] b1 b4 b5 supp_NUM[unfolded NUM_def supp_ltgt] NUM_def lam.fresh[unfolded fresh_def] fresh_def b6
lemmas app = Ltgt1_app

lemma NUM:
  shows "NUM \<cdot> \<lbrace>M\<rbrace> \<approx> \<lbrace>\<lbrace>M\<rbrace>\<rbrace>"
proof (induct M rule: lam.induct)
  case (Var n)
  have "NUM \<cdot> \<lbrace>Var n\<rbrace> = NUM \<cdot> (VAR \<cdot> Var n)" by simp
  also have "... = \<guillemotleft>[\<guillemotleft>[A1,A2,A3]\<guillemotright>]\<guillemotright> \<cdot> (VAR \<cdot> Var n)" by simp
  also have "... \<approx> VAR \<cdot> Var n \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using app .
  also have "... \<approx> \<guillemotleft>[A1,A2,A3]\<guillemotright> \<cdot> Umn 2 2 \<cdot> Var n \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using VAR_app .
  also have "... \<approx> A1 \<cdot> Var n \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using U_app by simp
  also have "... \<approx> F1 \<cdot> Var n" using A_app(1) .
  also have "... \<approx> APP \<cdot> \<lbrace>VAR\<rbrace> \<cdot> (VAR \<cdot> Var n)" using F_app(1) .
  also have "... = \<lbrace>\<lbrace>Var n\<rbrace>\<rbrace>" by simp
  finally show "NUM \<cdot> \<lbrace>Var n\<rbrace> \<approx> \<lbrace>\<lbrace>Var n\<rbrace>\<rbrace>".
next
  case (App M N)
  assume IH: "NUM \<cdot> \<lbrace>M\<rbrace> \<approx> \<lbrace>\<lbrace>M\<rbrace>\<rbrace>" "NUM \<cdot> \<lbrace>N\<rbrace> \<approx> \<lbrace>\<lbrace>N\<rbrace>\<rbrace>"
  have "NUM \<cdot> \<lbrace>M \<cdot> N\<rbrace> = NUM \<cdot> (APP \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace>)" by simp
  also have "... = \<guillemotleft>[\<guillemotleft>[A1,A2,A3]\<guillemotright>]\<guillemotright> \<cdot> (APP \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace>)" by simp
  also have "... \<approx> APP \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace> \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using app .
  also have "... \<approx> \<guillemotleft>[A1,A2,A3]\<guillemotright> \<cdot> Umn 2 1 \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace> \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using APP_app .
  also have "... \<approx> A2 \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace> \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using U_app by simp
  also have "... \<approx> F2 \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace> \<cdot> NUM" using A_app(2) by simp
  also have "... \<approx> APP \<cdot> (APP \<cdot> \<lbrace>APP\<rbrace> \<cdot> (NUM \<cdot> \<lbrace>M\<rbrace>)) \<cdot> (NUM \<cdot> \<lbrace>N\<rbrace>)" using F_app(2) .
  also have "... \<approx> APP \<cdot> (APP \<cdot> \<lbrace>APP\<rbrace> \<cdot> (\<lbrace>\<lbrace>M\<rbrace>\<rbrace>)) \<cdot> (NUM \<cdot> \<lbrace>N\<rbrace>)" using IH by simp
  also have "... \<approx> \<lbrace>\<lbrace>M \<cdot> N\<rbrace>\<rbrace>" using IH by simp
  finally show "NUM \<cdot> \<lbrace>M \<cdot> N\<rbrace> \<approx> \<lbrace>\<lbrace>M \<cdot> N\<rbrace>\<rbrace>".
next
  case (Lam x P)
  assume IH: "NUM \<cdot> \<lbrace>P\<rbrace> \<approx> \<lbrace>\<lbrace>P\<rbrace>\<rbrace>"
  have "NUM \<cdot> \<lbrace>\<integral> x. P\<rbrace> = NUM \<cdot> (Abs \<cdot> \<integral> x. \<lbrace>P\<rbrace>)" by simp
  also have "... = \<guillemotleft>[\<guillemotleft>[A1,A2,A3]\<guillemotright>]\<guillemotright> \<cdot> (Abs \<cdot> \<integral> x. \<lbrace>P\<rbrace>)" by simp
  also have "... \<approx> Abs \<cdot> (\<integral> x. \<lbrace>P\<rbrace>) \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using app .
  also have "... \<approx> \<guillemotleft>[A1,A2,A3]\<guillemotright> \<cdot> Umn 2 0 \<cdot> (\<integral> x. \<lbrace>P\<rbrace>) \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using Abs_app .
  also have "... \<approx> A3 \<cdot> (\<integral> x. \<lbrace>P\<rbrace>) \<cdot> \<guillemotleft>[A1,A2,A3]\<guillemotright>" using U_app by simp
  also have "... \<approx> F3 \<cdot> (\<integral> x. \<lbrace>P\<rbrace>) \<cdot> \<guillemotleft>[\<guillemotleft>[A1,A2,A3]\<guillemotright>]\<guillemotright>" using A_app(3) .
  also have "... = F3 \<cdot> (\<integral> x. \<lbrace>P\<rbrace>) \<cdot> NUM" by simp
  also have "... \<approx> APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> \<integral> x. (NUM \<cdot> ((\<integral> x. \<lbrace>P\<rbrace>) \<cdot> Var x)))" by (rule F3_app) simp_all
  also have "... \<approx> APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> \<integral> x. (NUM \<cdot> \<lbrace>P\<rbrace>))" using beta_app by simp
  also have "... \<approx> APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> \<integral> x. \<lbrace>\<lbrace>P\<rbrace>\<rbrace>)" using IH by simp
  also have "... = \<lbrace>\<lbrace>\<integral> x. P\<rbrace>\<rbrace>" by simp
  finally show "NUM \<cdot> \<lbrace>\<integral> x. P\<rbrace> \<approx> \<lbrace>\<lbrace>\<integral> x. P\<rbrace>\<rbrace>" .
qed

lemmas [simp] = Ap NUM
lemmas [simp del] = fresh_def NUM_def

theorem SFP:
  fixes F :: lam
  shows "\<exists>X. X \<approx> F \<cdot> \<lbrace>X\<rbrace>"
proof -
  obtain x :: name where [simp]:"atom x \<sharp> F" using obtain_fresh by blast
  def W \<equiv> "\<integral>x. (F \<cdot> (APP \<cdot> Var x \<cdot> (NUM \<cdot> Var x)))"
  def X \<equiv> "W \<cdot> \<lbrace>W\<rbrace>"
  have a: "X = W \<cdot> \<lbrace>W\<rbrace>" unfolding X_def ..
  also have "... = (\<integral>x. (F \<cdot> (APP \<cdot> Var x \<cdot> (NUM \<cdot> Var x)))) \<cdot> \<lbrace>W\<rbrace>" unfolding W_def ..
  also have "... \<approx> F \<cdot> (APP \<cdot> \<lbrace>W\<rbrace> \<cdot> (NUM \<cdot> \<lbrace>W\<rbrace>))" by simp
  also have "... \<approx> F \<cdot> (APP \<cdot> \<lbrace>W\<rbrace> \<cdot> \<lbrace>\<lbrace>W\<rbrace>\<rbrace>)" by simp
  also have "... \<approx> F \<cdot> \<lbrace>W \<cdot> \<lbrace>W\<rbrace>\<rbrace>" by simp
  also have "... = F \<cdot> \<lbrace>X\<rbrace>" unfolding X_def ..
  finally show ?thesis by blast
qed

end
