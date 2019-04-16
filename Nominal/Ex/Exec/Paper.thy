(*<*)
theory Paper imports Lambda_Exec begin

notation (latex output)
      Name ("\<nu>_")
  and subst ("_ [_ := _]" [90, 90, 90] 90)
  and Lam ("\<^raw:$\lambda$>_. _" [50, 50] 50)
(*  and atom ("_")*)
  and swap ("'(_ _')" [1000, 1000] 1000)
(*and Umn ("\<^raw:$U^{\mbox{>_\<^raw:}}_{\mbox{>_\<^raw:}}$>" [205,205] 200)*)
  and all (binder "\<forall>" 10)
  and fresh ("_ \<FRESH> _" [55, 55] 55)
  and Set.empty ("\<emptyset>")

declare [[show_question_marks = false]]
(*>*)

section {* Introduction *}

section {* General Algorithm *}

section {* Executing the Foundations of Nominal Logic *}

subsection {* Executable Permutations *}

text {*
\begin{itemize}
\item Definitions of permutation as a list: application of a permutation,
  validity of a permutation and equality of permutations
  @{thm [display, indent=5] perm_apply_def}
  @{thm [display, indent=5] valid_perm_def}
  @{thm [display, indent=5] perm_eq_def}
\item Quotient type
  @{text [display, indent=5] "quotient_type 'a gperm = \"('a \<times> 'a) list\" / partial: \"perm_eq\""}
\item Definitions of composing permutations and inverse permutation as well
  as showing that:
  @{text [display, indent=5] "instantiation gperm :: (type) group_add"}
\item Proper representation and abstraction functions to make the @{text "code_abstype"}
  @{thm [display, indent=5] dest_perm_raw_def}
  @{thm [display, indent=5] mk_perm_raw_def}
\item Code abstract equations of permutation composition, inverse, zero, swapping etc
\end{itemize} *}

subsection {* Sort-respecting Permutations *}

text {*
\begin{itemize}
\item The type of sorted atoms
\item Definition of sort-respecting
  @{thm [display, indent=5] sort_respecting_def}
\item typedef and definitions of the basic operations
\item showing that the sort-respecting ones are also a group\_add and that the
  code equations can be reused.
\end{itemize}
*}

subsection {* Concrete atom types *}

text {*
\begin{itemize}
\item bijection to natural numbers
  @{thm [display, indent=5] Name_def}
  @{thm [display, indent=5] nat_of_name_def}
\item @{text "code_datatype"}
\item equality of variables and a code equation for concrete variables
  @{thm [display, indent=5] equal_name_def}
  @{thm [display, indent=5] equal_name_code}
\item code equations for @{term atom} and application of a permutation
  @{thm [display, indent=5] atom_name_code}
  @{thm [display, indent=5] permute_name_code}
\end{itemize}
 *}

section {* Executing the Lambda Terms *}

text {*
\begin{itemize}
\item Defining a representation type: LN
\item Abstraction with an accumulator
  @{thm [display, indent=5] ln_lam_aux.simps}
  @{thm [display, indent=5] ln_lam_def}
\item Representation, with a helper
  @{thm [display, indent=5] subst_ln_nat.simps}
  @{thm [display, indent=5] lam_ln_ex.simps}
\item A helper function \& proof that equal:
  @{thm [display, indent=5] lam_ln_aux.simps}
  @{thm [display, indent=5] lam_ln_def}
  @{thm [display, indent=5] lam_ln_ex}
\item Code abstype
  @{thm [display, indent=5] ln_abstype}
\item equality and permutations for the abstract type
  @{thm [display, indent=5] equal_lam_def}
  @{thm [display, indent=5] lam_ln_ex.eqvt[symmetric]}
\end{itemize}
*}

subsection {* Executing substitution *}

text {*
\begin{itemize}
\item Substitution on the representation:
  @{thm [display, indent=5] subst_ln.simps}
\item equality of substitutions:
  @{thm [display, indent=5] subst_code}
\end{itemize}

Example of execution:

@{text value} @{term "subst ((N0 \<leftrightarrow> N1) \<bullet> (App (Var N0) (Lam [N1]. (Var N1)))) N1 (Var N0)"}

*}

section {* Conclusion\label{sec:conclusion} *}

subsection {* Future Work *}

text {*
  Efficiency: Use more efficient representation for permutations than
  lists. Might be useful for bigger permutations, but for permuttaions
  of up to 3 elements does not make much sense *}

subsection {* Related Work *}

text {*
  Locally Nameless~\cite{LocallyNameless}
*}

(*<*)
end
(*>*)
