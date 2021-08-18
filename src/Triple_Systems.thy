(* Title: Triple_System.thy
   Author: Chelsea Edmonds
*)

theory Triple_Systems imports Resolvable_Designs
begin

section \<open>Triple Systems \<close>
text \<open>One of the first ever types of designs studied investigated designs with block size of 3. 
Ever since, they have remained an important class of designs

Note: Main definitions only. Lemmas out of scope of initial design theory work \<close>

locale triple_system = block_design \<V> \<B> 3 for point_set ("\<V>") and block_collection ("\<B>")

subsection \<open>Steiner Triple Systems \<close>
text \<open>One of the most studied types of BIBD's \<close>

locale STS = bibd \<V> \<B> 3 1 for point_set ("\<V>") and block_collection ("\<B>")

sublocale STS \<subseteq> triple_system
  by (unfold_locales)

text \<open>Partial Steiner Triple systems are those that don't strictly meet the index 
requirement of a bibd \<close>
locale PTS = t_packing_design \<V> \<B> 3 2 1 for point_set ("\<V>") and block_collection ("\<B>")

begin

definition block_leave:: "'a set \<Rightarrow> 'a set multiset" where
"block_leave bl \<equiv> mset_set { ps . ps \<subseteq> \<V> \<and> (card ps = 2) \<and> \<not> ps \<subseteq> bl}"

definition leave :: "'a set multiset" where
"leave \<equiv> \<Sum>bl \<in># \<B>. block_leave bl"

lemma pts_leave_count: "count leave ps = 1 - points_index \<B> ps"
  oops

end

sublocale STS \<subseteq> PTS
  by unfold_locales

subsection \<open>Kirkman Designs \<close>
text \<open> The original triple system is a resolvable STS \<close>

locale KTS = STS \<V> \<B> + rbibd \<V> \<B> \<P> 3 1 for point_set ("\<V>") and block_collection ("\<B>") and partition ("\<P>")
begin

corollary kirkman_condition_on_v: "3 dvd \<v>"
  using resolvable_necessary_cond_v by simp

end

(* Requires a group theoretic proof *)
lemma (in STS) kirkman_condition_on_v_sufficient: "\<v> mod 6 \<equiv> 3 \<Longrightarrow> KTS \<V> \<B> \<P>"
  oops
end