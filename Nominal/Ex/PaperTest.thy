theory PaperTest
imports "../Nominal2"
begin

atom_decl name 

datatype trm = 
  Const "string"
| Var "name"
| App "trm" "trm"
| Lam "name" "trm"  ("Lam [_]. _" [100, 100] 100)

fun
  subst :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"  ("_[_::=_]" [100,100,100] 100)
where
  "(Var x)[y::=p] = (if x=y then (App (App (Const ''unpermute'') (Var p)) (Var x)) else (Var x))"
| "(App t\<^isub>1 t\<^isub>2)[y::=p] = App (t\<^isub>1[y::=p]) (t\<^isub>2[y::=p])"
| "(Lam [x].t)[y::=p] = (if x=y then (Lam [x].t) else Lam [x].(t[y::=p]))"
| "(Const n)[y::=p] = Const n"

datatype utrm = 
  UConst "string"
| UnPermute "name" "name"
| UVar "name"
| UApp "utrm" "utrm"
| ULam "name" "utrm"  ("ULam [_]. _" [100, 100] 100)

fun
  usubst :: "utrm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> utrm"  ("_[_:::=_]" [100,100,100] 100)
where
  "(UVar x)[y:::=p] = (if x=y then UnPermute p x else (UVar x))"
| "(UApp t\<^isub>1 t\<^isub>2)[y:::=p] = UApp (t\<^isub>1[y:::=p]) (t\<^isub>2[y:::=p])"
| "(ULam [x].t)[y:::=p] = (if x=y then (ULam [x].t) else ULam [x].(t[y:::=p]))"
| "(UConst n)[y:::=p] = UConst n"
| "(UnPermute x q)[y:::=p] = UnPermute x q"

function
  ss :: "trm \<Rightarrow> nat"
where
  "ss (Var x) = 1"
| "ss (Const s) = 1"
| "ss (Lam [x].t) = 1 + ss t"
| "ss (App (App (Const ''unpermute'') (Var p)) (Var x)) = 1"
| "\<not>(\<exists>p x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x)) \<Longrightarrow> ss (App t1 t2) = 1 + ss t1 + ss t2"
defer
apply(simp_all)
apply(auto)[1]
apply(case_tac x)
apply(simp_all)
apply(auto)
apply(blast)
done

termination
  apply(relation "measure (\<lambda>t. size t)")
  apply(simp_all)
  done

fun
  uss :: "utrm \<Rightarrow> nat"
where
  "uss (UVar x) = 1"
| "uss (UConst s) = 1"
| "uss (ULam [x].t) = 1 + uss t"
| "uss (UnPermute x y) = 1"
| "uss (UApp t1 t2) = 1 + uss t1 + uss t2"

lemma trm_uss:
  shows "uss (t[x:::=p]) = uss t"
apply(induct rule: uss.induct)
apply(simp_all)
done

inductive
  ufree :: "utrm \<Rightarrow> bool"
where
  "ufree (UVar x)"
| "s \<noteq> ''unpermute'' \<Longrightarrow> ufree (UConst s)"
| "ufree t \<Longrightarrow> ufree (ULam [x].t)"
| "ufree (UnPermute x y)"
| "\<lbrakk>ufree t1; ufree t2\<rbrakk> \<Longrightarrow> ufree (UApp t1 t2)"

fun
  trans :: "utrm \<Rightarrow> trm" ("\<parallel>_\<parallel>" [100] 100)
where
  "\<parallel>(UVar x)\<parallel> = Var x"
| "\<parallel>(UConst x)\<parallel> = Const x"
| "\<parallel>(UnPermute p x)\<parallel> = (App (App (Const ''unpermute'') (Var p)) (Var x))"
| "\<parallel>(ULam [x].t)\<parallel> = Lam [x].(\<parallel>t\<parallel>)"
| "\<parallel>(UApp t1 t2)\<parallel> = App (\<parallel>t1\<parallel>) (\<parallel>t2\<parallel>)"

function
  utrans :: "trm \<Rightarrow> utrm" ("\<lparr>_\<rparr>" [90] 100)
where
  "\<lparr>Var x\<rparr> = UVar x"
| "\<lparr>Const x\<rparr> = UConst x"
| "\<lparr>Lam [x].t\<rparr> = ULam [x].\<lparr>t\<rparr>"
| "\<lparr>App (App (Const ''unpermute'') (Var p)) (Var x)\<rparr> = UnPermute p x"
| "\<not>(\<exists>p x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x)) \<Longrightarrow> \<lparr>App t1 t2\<rparr> = UApp (\<lparr>t1\<rparr>) (\<lparr>t2\<rparr>)"
defer
apply(simp_all)
apply(auto)[1]
apply(case_tac x)
apply(simp_all)
apply(auto)
apply(blast)
done

termination
  apply(relation "measure (\<lambda>t. size t)")
  apply(simp_all)
  done


lemma elim1:
  "ufree t \<Longrightarrow> \<parallel>t\<parallel> \<noteq>(Const ''unpermute'')"
apply(erule ufree.induct)
apply(auto)
done

lemma elim2:
  "ufree t \<Longrightarrow> \<not>(\<exists>p. \<parallel>t\<parallel> = App (Const ''unpermute'') (Var p))"
apply(erule ufree.induct)
apply(auto dest: elim1)
done

lemma ss1:
  "ufree t \<Longrightarrow> uss t = ss (\<parallel>t\<parallel>)"
apply(erule ufree.induct)
apply(simp_all)
apply(subst ss.simps)
apply(auto)
apply(drule elim2)
apply(auto)
done

lemma trans1:
  shows "\<parallel>\<lparr>t\<rparr>\<parallel> = t"
apply(induct t)
apply(simp)
apply(simp)
prefer 2
apply(simp)
apply(case_tac "(\<exists>p x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x))")
apply(erule exE)+
apply(simp)
apply(simp)
done

lemma trans_subst:
  shows "\<lparr>t[x ::= p]\<rparr> = \<lparr>t\<rparr>[x :::= p]"
apply(induct rule: subst.induct)
apply(simp)
defer
apply(simp)
apply(simp)
apply(simp)
apply(case_tac "(t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x))")
apply(erule exE)+
apply(simp only:)
apply(subst utrans.simps)
apply(subst usubst.simps)
apply(case_tac "xa = x")
apply(subst (asm) subst.simps)
apply(simp only:)
apply(subst (asm) utrans.simps)
apply(simp only: usubst.simps)
apply(simp)
apply(auto)[1]
apply(case_tac "pa = x")
apply(simp)
prefer 2
apply(simp)
apply(simp)
done

lemma 
  "ss (t[x ::= p]) = ss t"
apply(subst (2) trans1[symmetric])
apply(subst ss1[symmetric])


fun
  fr :: "trm \<Rightarrow> name set"
where
  "fr (Var x) = {x}"
| "fr (Const s) = {}"
| "fr (Lam [x].t) = fr t - {x}"
| "fr (App t1 t2) = fr t1 \<union> fr t2"

function
  sfr :: "trm \<Rightarrow> name set"
where
  "sfr (Var x) = {}"
| "sfr (Const s) = {}"
| "sfr (Lam [x].t) = sfr t - {x}"
| "sfr (App (App (Const ''unpermute'') (Var p)) (Var x)) = {p, x}"
| "\<not>(\<exists>p x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x)) \<Longrightarrow> sfr (App t1 t2) = sfr t1 \<union> sfr t2"
defer
apply(simp_all)
apply(auto)[1]
apply(case_tac x)
apply(simp_all)
apply(auto)
apply(blast)
done

termination
  apply(relation "measure (\<lambda>t. size t)")
  apply(simp_all)
  done

function
  ss :: "trm \<Rightarrow> nat"
where
  "ss (Var x) = 1"
| "ss (Const s) = 1"
| "ss (Lam [x].t) = 1 + ss t"
| "ss (App (App (Const ''unpermute'') (Var p)) (Var x)) = 1"
| "\<not>(\<exists>p x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x)) \<Longrightarrow> ss (App t1 t2) = 1 + ss t1 + ss t2"
defer
apply(simp_all)
apply(auto)[1]
apply(case_tac x)
apply(simp_all)
apply(auto)
apply(blast)
done 

termination
  apply(relation "measure (\<lambda>t. size t)")
  apply(simp_all)
  done

inductive
  improper :: "trm \<Rightarrow> bool"
where
  "improper (App (App (Const ''unpermute'') (Var p)) (Var x))"
| "improper p x t \<Longrightarrow> improper p x (Lam [y].t)"
| "\<lbrakk>improper p x t1; improper p x t2\<rbrakk> \<Longrightarrow> improper p x (App t1 t2)"

lemma trm_ss:
  shows "\<not>improper p x t \<Longrightarrow> ss (t[x::= p]) = ss t"
apply(induct rule: ss.induct)
apply(simp)
apply(simp)
apply(simp)
apply(auto)[1]
apply(case_tac "improper p x t")
apply(drule improper.intros(2))
apply(blast)
apply(simp)
using improper.intros(1)
apply(blast)
apply(erule contrapos_pn)
thm contrapos_np
apply(simp)
apply(auto)[1]
apply(simp)
apply(erule disjE)
apply(erule conjE)+
apply(subst ss.simps)
apply(simp)
apply(rule disjI1)
apply(rule allI)
apply(rule notI)

apply(simp del: ss.simps)
apply(erule disjE)
apply(subst ss.simps)
apply(simp)
apply(simp only: subst.simps)
apply(subst ss.simps)
apply(simp del: ss.simps)
apply(rule conjI)
apply(rule impI)
apply(erule conjE)
apply(erule exE)+
apply(subst ss.simps)
apply(simp)
apply(auto)[1]
apply(simp add: if_splits)
apply()

function
  simp :: "name \<Rightarrow> trm \<Rightarrow> trm"
where
  "simp p (Const c) = (Const c)"
| "simp p (Var x) = App (App (Const ''permute'') (Var p)) (Var x)"
| "simp p (App t1 t2) = (if ((\<exists>x. t1 = App (Const ''unpermute'') (Var p) \<and> t2 = (Var x))) 
                         then t2
                         else App (simp p t1) (simp p t2))"
| "simp p (Lam [x].t) = Lam [x]. (simp p (t[x ::= p]))"
apply(pat_completeness)
apply(simp_all)
apply(auto)
done

termination
apply(relation "measure (\<lambda>(_, t). size t)")
apply(simp_all)

end
