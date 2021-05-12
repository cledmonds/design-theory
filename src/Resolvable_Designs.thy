theory Resolvable_Designs imports BIBD
begin

section \<open>Resolvable Designs \<close>
text \<open>Resolvable designs have further structure, and can be "resolved" into 
a set of resolution classes. A resolution class is a subset of blocks which exactly partitions the point set \<close>

subsection \<open>Resolutions and Resolution Classes \<close>

context incidence_system
begin 

definition resolution_class :: "'a set set \<Rightarrow> bool" where
"resolution_class S \<longleftrightarrow> partition_on \<V> S \<and> (\<forall> bl \<in> S . bl \<in># \<B>)"

lemma resolution_classI [intro]: "partition_on \<V>  S \<Longrightarrow> (\<And> bl . bl \<in> S \<Longrightarrow> bl \<in># \<B>) \<Longrightarrow> resolution_class S"
  by (simp add: resolution_class_def)

lemma resolution_classD1: "resolution_class S \<Longrightarrow> partition_on \<V> S"
  by (simp add: resolution_class_def)

lemma resolution_classD2: "resolution_class S \<Longrightarrow>  bl \<in> S \<Longrightarrow> bl \<in># \<B>"
  by (simp add: resolution_class_def)

lemma resolution_class_empty_iff: "resolution_class {} \<longleftrightarrow> \<V>  = {}"
  by (auto simp add: resolution_class_def partition_on_def)

lemma resolution_class_complete: "\<V>  \<noteq> {} \<Longrightarrow> \<V>  \<in># \<B> \<Longrightarrow> resolution_class {\<V>}"
  by (auto simp add: resolution_class_def partition_on_space)

lemma resolution_class_union: "resolution_class S \<Longrightarrow> \<Union>S = \<V> "
  by (simp add: resolution_class_def partition_on_def)

lemma (in design) resolution_class_sum_card: "resolution_class S \<Longrightarrow> (\<Sum>bl \<in> S . card bl) = \<v>"
  apply (auto simp add: resolution_class_def)
  using resolution_class_union partition_on_def card_Union_disjoint finite_blocks by fastforce 

lemma (in finite_incidence_system) resolution_class_finite: "resolution_class S \<Longrightarrow> finite S"
  using finite_elements finite_sets by (auto simp add: resolution_class_def)

definition resolution:: "'a set multiset multiset \<Rightarrow> bool" where
"resolution P \<longleftrightarrow> partition_on_mset \<B> P \<and> (\<forall> S \<in># P . distinct_mset S \<and> resolution_class (set_mset S))"

lemma resolutionI : "partition_on_mset \<B> P \<Longrightarrow> (\<And> S . S \<in>#P \<Longrightarrow> distinct_mset S) \<Longrightarrow> (\<And> S . S\<in># P \<Longrightarrow> resolution_class (set_mset S)) \<Longrightarrow> resolution P"
  by (simp add: resolution_def)

lemma (in proper_design) resolution_blocks: "distinct_mset \<B> \<Longrightarrow> disjoint (set_mset \<B>) \<Longrightarrow> \<Union>(set_mset \<B>) = \<V> \<Longrightarrow> resolution {#\<B>#}"
  apply (auto simp add: resolution_def resolution_class_def partition_on_mset_def partition_on_def design_blocks_nempty) 
  using blocks_nempty by auto

end

subsection \<open>Resolvable Design Locale \<close>
locale resolvable_design = design + 
  fixes partition :: "'a set multiset multiset" ("\<P>")
  assumes resolvable: "resolution \<P>"
begin

lemma resolutionD1: "partition_on_mset \<B> \<P>"
  using resolvable by (simp add: resolution_def)

lemma resolutionD2: "S \<in>#\<P> \<Longrightarrow> distinct_mset S" 
  using resolvable by (simp  add: resolution_def)

lemma resolutionD3: " S\<in># \<P> \<Longrightarrow> resolution_class (set_mset S)"
  using resolvable by (simp add: resolution_def)

lemma resolution_class_blocks_disjoint: "S \<in># \<P> \<Longrightarrow> disjoint (set_mset S)"
  using resolutionD3 by (simp add: partition_on_def resolution_class_def) 

lemma resolution_not_empty: "\<B> \<noteq> {#} \<Longrightarrow> \<P> \<noteq> {#}"
  using partition_on_mset_not_empty resolutionD1 by auto 

lemma resolution_blocks_subset: "S \<in># \<P> \<Longrightarrow> S \<subseteq># \<B>"
  using partition_on_mset_subsets resolutionD1 by auto

end

lemma (in incidence_system) resolvable_designI [intro]: "resolution \<P> \<Longrightarrow> design \<V> \<B> \<Longrightarrow> resolvable_design \<V> \<B> \<P>"
  by (simp add: resolvable_design.intro resolvable_design_axioms.intro)

subsection \<open>Resolvable Block Design \<close>

locale r_block_design = resolvable_design + block_design
begin
lemma resolution_class_blocks_constant_size: "S \<in># \<P> \<Longrightarrow> bl \<in># S \<Longrightarrow> card bl = \<k>"
  by (metis resolutionD3 resolution_classD2 uniform_alt_def_all)

lemma resolution_class_size1: 
  assumes "S \<in># \<P>"
  shows "\<v> = \<k> * size S"
proof - 
  have "(\<Sum>bl \<in># S . card bl) = (\<Sum>bl \<in> (set_mset S) . card bl)" using resolutionD2 assms
    by (simp add:  sum_unfold_sum_mset)
  then have eqv: "(\<Sum>bl \<in># S . card bl) = \<v>" using resolutionD3 assms resolution_class_sum_card
    by presburger 
  have "(\<Sum>bl \<in># S . card bl) = (\<Sum>bl \<in># S . \<k>)" using resolution_class_blocks_constant_size assms by auto
  thus ?thesis using eqv
    by (metis mult.commute sum_mset_constant) 
qed

lemma resolution_class_size2: 
  assumes "S \<in># \<P>"
  shows "size S = \<v> div \<k>"
  using resolution_class_size1 assms
  by (metis nonzero_mult_div_cancel_left not_one_le_zero k_non_zero)

lemma resolvable_necessary_cond_v: "\<k> dvd \<v>"
proof -
  obtain S where s_in: "S \<in>#\<P>" using resolution_not_empty design_blocks_nempty by blast
  then have "\<k> * size S = \<v>" using resolution_class_size1  by simp 
  thus ?thesis by (metis dvd_triv_left) 
qed

end

subsection \<open> Resolvable BIBD's \<close>
locale rbibd = resolvable_design + bibd

sublocale rbibd \<subseteq> r_block_design \<V> \<B> \<P> \<k>
  by (unfold_locales)

context rbibd begin

lemma resolvable_design_num_res_classes: "size \<P> = \<r>"
proof - 
  have k_ne0: "\<k> \<noteq> 0" using k_non_zero by auto 
  have f1: "\<b> = (\<Sum>S \<in># \<P> . size S)"
    by (metis partition_on_msetD1 resolutionD1 size_big_union_sum)
  then have "\<b> = (\<Sum>S \<in># \<P> . \<v> div \<k>)" using resolution_class_size2 f1 by auto
  then have f2: "\<b> = (size \<P>) *  (\<v> div \<k>)" by simp
  then have "size \<P> = \<b> div (\<v> div \<k>)"
    using b_non_zero by auto 
  then have "size \<P> = (\<b> * \<k>) div \<v>"
    by (metis f2 div_div_div_same div_dvd_div dvd_triv_right k_ne0 nonzero_mult_div_cancel_right resolvable_necessary_cond_v)
  thus ?thesis using necessary_condition_two
    by (metis nonzero_mult_div_cancel_left not_one_less_zero tdesign_min_v) 
qed

lemma resolvable_necessary_cond_b: "\<r> dvd \<b>"
proof -
  have f1: "\<b> = (\<Sum>S \<in># \<P> . size S)"
    by (metis partition_on_msetD1 resolutionD1 size_big_union_sum)
  then have "\<b> = (\<Sum>S \<in># \<P> . \<v> div \<k>)" using resolution_class_size2 f1 by auto
  thus ?thesis using resolvable_design_num_res_classes by simp
qed

text \<open> Boses inequality is an important theorem on RBIBD's. This is a proof 
of an alternate statement of the thm, which does not require a linear algebraic approach \<close>
lemma bose_inequality_alternate: "\<b> \<ge> \<v> + \<r> - 1 \<longleftrightarrow> \<r> \<ge> \<k> + \<Lambda>"
proof - 
  have "\<b> \<ge> \<v> + \<r> - 1 \<Longrightarrow> \<b> > \<v>"
    using index_lt_replication index_not_zero by linarith
  then have r_ge_k_left: "\<b> \<ge> \<v> + \<r> - 1 \<Longrightarrow> \<r> > \<k>" using necess_cond_one_param_balance
    by blast
  then have r_k_not_zero_left: "\<b> \<ge> \<v> + \<r> - 1 \<Longrightarrow> \<r> - \<k> > 0"
    by simp 
  have "\<r> \<ge> \<k> + \<Lambda> \<Longrightarrow> \<r> > \<k>" using index_not_zero
    by linarith 
  then have r_k_not_zero_right: "\<r> \<ge> \<k> + \<Lambda> \<Longrightarrow> \<r> - \<k> > 0" by simp
  have kdvd: "\<k> dvd (\<v> * (\<r> - \<k>))"
    using necessary_condition_two by (simp add: right_diff_distrib') 
  have v_eq: "\<v> = (\<r> * (\<k> - 1) + \<Lambda> ) div \<Lambda>" using necessary_condition_one
    using index_not_zero by auto
  then have " \<Lambda> dvd (\<r> * (\<k> - 1) + \<Lambda> )"
    using necessary_condition_one by auto 
  then have ldvd: " \<And> x. \<Lambda> dvd (x * (\<r> * (\<k> - 1) + \<Lambda>))" by auto
  have "(\<b> \<ge> \<v> + \<r> - 1) \<longleftrightarrow> ((\<v> * \<r>) div \<k> \<ge> \<v> + \<r> - 1)"
    using necessary_condition_two k_non_zero by auto
  also have  "... \<longleftrightarrow> (((\<v> * \<r>) - (\<v> * \<k>)) div \<k> \<ge> \<r> - 1)"
    using  k_non_zero div_mult_self3 k_non_zero necessary_condition_two by auto
  also have f2: " ... \<longleftrightarrow> ((\<v> * ( \<r> - \<k>)) \<ge> \<k> * ( \<r> - 1))" 
    using k_non_zero kdvd by (auto simp add: int_distrib(3) mult_of_nat_commute) 
  also have "... \<longleftrightarrow> ((((\<r> * (\<k> - 1) + \<Lambda> ) div \<Lambda>) * (\<r> - \<k>)) \<ge> \<k> * (\<r> - 1))"
    using v_eq by presburger 
  also have "... \<longleftrightarrow> ( (\<r> - \<k>) * ((\<r> * (\<k> - 1) + \<Lambda> ) div \<Lambda>) \<ge> (\<k> * (\<r> - 1)))" 
    by (simp add: mult.commute)
  also have " ... \<longleftrightarrow> ( ((\<r> - \<k>) * (\<r> * (\<k> - 1) + \<Lambda> )) div \<Lambda> \<ge> (\<k> * (\<r> - 1)))"
    by (metis div_mult_swap dvd_add_triv_right_iff dvd_triv_left necessary_condition_one) 
  also have " ... \<longleftrightarrow> (((\<r> - \<k>) * (\<r> * (\<k> - 1) + \<Lambda> ))  \<ge>  \<Lambda> * (\<k> * (\<r> - 1)))" 
    using ldvd by (smt dvd_mult_div_cancel index_not_zero mult_strict_left_mono) 
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * (\<r> * (\<k> - 1))) + ((\<r> - \<k>) * \<Lambda> )  \<ge>  \<Lambda> * (\<k> * (\<r> - 1)))" 
    by (simp add: distrib_left) 
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> \<Lambda> * \<k> * (\<r> - 1) - ((\<r> - \<k>) * \<Lambda> ))" 
    using mult.assoc by linarith 
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> (\<Lambda> * \<k> * \<r>) - (\<Lambda> * \<k>) - ((\<r> * \<Lambda>) -(\<k> * \<Lambda> )))" 
    using distrib_right by (simp add: distrib_left right_diff_distrib' left_diff_distrib') 
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> (\<Lambda>  * \<k> * \<r>)  - ( \<Lambda> * \<r>))" 
    by (simp add: mult.commute) 
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> (\<Lambda>  * (\<k> * \<r>))  - ( \<Lambda> * \<r>))" by linarith  
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> (\<Lambda>  * (\<r> * \<k>))  - ( \<Lambda> * \<r>))" 
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> (((\<r> - \<k>) * \<r> * (\<k> - 1)) \<ge> \<Lambda> * \<r> * ( \<k> - 1))"
    by (simp add: mult.assoc int_distrib(4)) 
  finally have "(\<b> \<ge> \<v> + \<r> - 1) \<longleftrightarrow> (\<r> \<ge> \<k> + \<Lambda>)"
    using index_lt_replication mult_right_le_imp_le r_gzero
    by (smt mult_cancel_right k_non_zero) 
  thus ?thesis by simp
qed
end
end