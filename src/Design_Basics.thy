theory Design_Basics imports Main Multisets_Extras "HOL-Library.Disjoint_Sets"
begin

section \<open> Design Theory Basics \<close>

subsection \<open> Initial setup \<close>

text \<open> Enable coercion of nats to ints to aid with reasoning on design properties \<close>
declare [[coercion_enabled]]
declare [[coercion "of_nat :: nat \<Rightarrow> int"]]

text \<open>Set up design theory type synomyns/abbreviations/notation for easy referencing \<close>

type_synonym 'a set_system = "'a set \<times> 'a set multiset"

abbreviation points :: "'a set_system \<Rightarrow> 'a set" 
  where "points D \<equiv> fst D"

abbreviation blocks :: "'a set_system \<Rightarrow> 'a set multiset"
  where "blocks D \<equiv> snd D"

subsection \<open> General Set System Properties \<close>
text \<open> Sets up some initial properties and definitions on set systems \<close>

abbreviation incomplete_block :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"incomplete_block V bl \<equiv> card bl < card V"

abbreviation order :: "'a set_system \<Rightarrow> int" where
"order S \<equiv> int (card (points S))"

subsection \<open> Incidence System \<close>

text \<open>An incidence system is defined to be a wellformed set system. i.e. each block is a subset
of the base point set. Alternatively, an incidence system can be looked at as the point set
and an incidence relation which indicates if they are in the same block \<close>

locale incidence_system = 
  fixes point_set :: "'a set" ("\<V>")
  fixes block_collection :: "'a set multiset" ("\<B>")
  assumes wellformed: "b \<in># \<B> \<Longrightarrow> b \<subseteq> \<V>"
begin

definition "\<I> \<equiv> { (x, b) . b \<in># \<B> \<and> x \<in> b}" (* incidence relation *)

definition incident :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
"incident p b \<equiv> (p, b) \<in> \<I>"

text \<open>Defines common notation used to indicate number of points ($v$) and number of blocks ($b$) \<close>
abbreviation "\<v> \<equiv> int (card \<V>)"

abbreviation "\<b> \<equiv> int (size \<B>)"

lemma incidence_alt_def: 
  assumes "p \<in> \<V>"
  assumes "b \<in># \<B>"
  shows "incident p b \<longleftrightarrow> p \<in> b"
  by (auto simp add: incident_def \<I>_def assms)

lemma wf_invalid_point: "x \<notin> \<V> \<Longrightarrow> b \<in># \<B> \<Longrightarrow> x \<notin> b"
  using wellformed by auto

lemma block_set_nempty_imp_block_ex: "\<B> \<noteq> {#} \<Longrightarrow> \<exists> bl . bl \<in># \<B>"
  by auto

abbreviation multiplicity :: "'a set \<Rightarrow> nat" where
"multiplicity b \<equiv> count \<B> b"

abbreviation incomplete_block :: "'a set \<Rightarrow> bool" where
"incomplete_block bl \<equiv> card bl < card \<V>"

abbreviation design_support :: "'a set set" where
"design_support \<equiv> set_mset \<B>"

end

subsection \<open> Finite Incidence Systems \<close>

text \<open> These simply require the point set to be finite.
As multisets are only defined to be finite, it is implied that the block set must be finite already \<close>

locale finite_incidence_system = incidence_system + 
  assumes finite_sets: "finite \<V>"

begin

lemma finite_blocks: "b \<in># \<B> \<Longrightarrow> finite b"
  using wellformed finite_sets finite_subset by blast 

lemma mset_points_distinct: "distinct_mset (mset_set \<V>)"
  using finite_sets by (simp add: distinct_mset_def)

lemma mset_points_distinct_diff_one: "distinct_mset (mset_set (\<V> - {x}))"
  by (meson count_mset_set_le_one distinct_mset_count_less_1)

lemma finite_design_support: "finite (design_support)"
  by auto 

end

subsection \<open> Designs \<close>

text \<open> There are many varied definitions of a design in literature. However, the most
commonly accepted definition is a finite point set, $V$ and collection of blocks $B$, where
no block in $B$ can be empty \<close>
locale design = finite_incidence_system +
  assumes blocks_nempty: "bl \<in># \<B> \<Longrightarrow> bl \<noteq> {}"
begin

lemma wf_design: "design \<V> \<B>"  by intro_locales

lemma wf_design_iff: "bl \<in># \<B> \<Longrightarrow> design \<V> \<B> \<longleftrightarrow> (bl \<subseteq> \<V> \<and> finite \<V> \<and> bl \<noteq> {})"
  using blocks_nempty wellformed finite_sets
  by (simp add: wf_design) 

lemma blocks_nempty_alt: "\<forall> bl \<in># \<B>. bl \<noteq> {}"
  using blocks_nempty by auto

lemma block_set_nempty_imp_points: "\<B> \<noteq> {#} \<Longrightarrow> \<V> \<noteq> {}"
  using wf_design wf_design_iff by auto

(* non-zero parameters *)
lemma b_non_zero_imp_v_non_zero: "\<b> > 0 \<Longrightarrow> \<v> > 0"
  using block_set_nempty_imp_points finite_sets by fastforce

lemma v_eq0_imp_b_eq_0: "\<v> = 0 \<Longrightarrow> \<b> = 0"
  using b_non_zero_imp_v_non_zero by auto

lemma block_size_lt_v: "bl \<in># \<B> \<Longrightarrow> card bl \<le> \<v>"
  by (simp add: card_mono finite_sets wellformed)

lemma design_cart_product_size: "size ((mset_set \<V>) \<times># \<B>) = \<v> * \<b>"
  by (simp add: size_cartesian_product) 

lemma order_v [simp]: "order (\<V>, \<B>) = \<v>"
  by simp 

end

lemma wf_design_implies: 
  assumes "(\<And> b . b \<in># \<B> \<Longrightarrow> b \<subseteq> V)"
  assumes "\<And> b . b \<in># \<B> \<Longrightarrow> b \<noteq> {}"
  assumes "finite V"
  assumes "\<B> \<noteq> {#}"
  assumes "V \<noteq> {}"
  shows "design V \<B>"
  using assms by (unfold_locales) simp_all

lemma (in incidence_system) finite_sysI[intro]: "finite \<V> \<Longrightarrow> finite_incidence_system \<V> \<B>"
  by (unfold_locales) simp_all

lemma (in finite_incidence_system) designI[intro]: "(\<And> b. b \<in># \<B> \<Longrightarrow> b \<noteq> {}) \<Longrightarrow> \<B> \<noteq> {#} \<Longrightarrow> \<V> \<noteq> {} \<Longrightarrow> design \<V> \<B>"
  by (unfold_locales) simp_all

subsection \<open> Core Property Definitions and Facts \<close>

subsubsection \<open> Replication Number\<close>

text \<open> The replication number for a point in a design is the number of blocks that point is incident with \<close>

definition point_replication_number :: "'a set multiset \<Rightarrow> 'a \<Rightarrow> int" (infix "rep" 75) where
"B rep x \<equiv> size {#b \<in># B . x \<in> b#}"

lemma max_point_rep: "B rep x \<le> size B"
  using size_filter_mset_lesseq by (simp add: point_replication_number_def)

lemma rep_number_g0_exists: assumes "B rep x > 0" obtains b where "b \<in># B" and "x \<in> b"
proof -
  have "size {#b \<in># B . x \<in> b#} > 0" using assms point_replication_number_def
    by (metis of_nat_0_less_iff)
  thus ?thesis
    by (metis filter_mset_empty_conv nonempty_has_size that) 
qed

lemma rep_number_on_set_def: "finite B \<Longrightarrow> (mset_set B) rep x = card {b \<in> B . x \<in> b}"
  by (simp add: point_replication_number_def)

context incidence_system
begin

lemma point_rep_number_alt_def: "\<B> rep x = size {# b \<in># \<B> . x \<in> b#}"
  by (simp add: point_replication_number_def)

lemma rep_number_non_zero_system_point: " \<B> rep x > 0 \<Longrightarrow> x \<in> \<V>"
  using rep_number_g0_exists wellformed
  by (metis wf_invalid_point) 

lemma point_rep_non_existance: "x \<notin> \<V> \<Longrightarrow> \<B> rep x = 0"
  using wf_invalid_point by (simp add:  point_replication_number_def filter_mset_empty_conv) 

lemma point_rep_number_inv: "size {# b \<in># \<B> . x \<notin> b #} = \<b> - (\<B> rep x)"
proof -
  have "\<b> = size {# b \<in># \<B> . x \<notin> b #} + size {# b \<in># \<B> . x \<in> b #}"
    using multiset_partition by (metis add.commute size_union)  
  thus ?thesis by (simp add: point_replication_number_def) 
qed

lemma point_rep_num_inv_non_empty: "(\<B> rep x) < \<b> \<Longrightarrow> \<B> \<noteq> {#} \<Longrightarrow> {# b \<in># \<B> . x \<notin> b #} \<noteq> {#}"
  by (metis diff_zero point_replication_number_def size_empty size_filter_neg verit_comp_simplify1(1))

end

subsubsection \<open>Point Index \<close>

text \<open>The point index of a subset of points in a design, is the number of times those points 
occur together in a block of the design\<close>
definition points_index :: "'a set multiset \<Rightarrow> 'a set \<Rightarrow> nat" where
"points_index B ps \<equiv> size {#b \<in># B . ps \<subseteq> b#}"

lemma (in incidence_system) points_index_alt_def: "points_index \<B> ps = size {#b \<in># \<B> . ps \<subseteq> b#}"
  by (simp add: points_index_def)

lemma (in finite_incidence_system) block_size_lt_order: "bl \<in># \<B> \<Longrightarrow> card bl \<le> card \<V>"
  using wellformed by (simp add: card_mono finite_sets)  

lemma card_subset_not_gt_card: "finite A \<Longrightarrow> card ps > card A \<Longrightarrow> \<not> (ps \<subseteq> A)"
  using card_mono leD by auto

lemma points_index_empty: "points_index {#} ps = 0"
  by (simp add: points_index_def)

lemma (in finite_incidence_system) points_index_zero: assumes "card ps > card \<V>" shows "points_index \<B> ps = 0"
proof -
  have "{#b \<in># \<B> . ps \<subseteq> b#} = {#}" using block_size_lt_order card_subset_not_gt_card finite_sets assms
    by (metis (mono_tags, lifting) Multiset.set_mset_filter mem_Collect_eq multiset_nonemptyE order.trans wellformed) 
  thus ?thesis using points_index_alt_def
    by simp
qed

lemma (in incidence_system) points_index_ps_nin: "\<not> (ps \<subseteq> \<V>) \<Longrightarrow> points_index \<B> ps = 0"
  using points_index_alt_def filter_mset_empty_conv in_mono size_empty subsetI wf_invalid_point
  by metis 

lemma (in design) points_index_subset: "x \<subseteq># {#bl \<in># \<B> . ps \<subseteq> bl#} \<Longrightarrow> ps \<subseteq> \<V> \<Longrightarrow> (points_index \<B> ps) \<ge> (size x)"
  by (simp add: points_index_def size_mset_mono)

lemma (in incidence_system) points_index_count_bl: "multiplicity bl \<ge> n \<Longrightarrow> ps \<subseteq> bl \<Longrightarrow>  count {#bl \<in># \<B> . ps \<subseteq> bl#} bl \<ge> n"
  by simp

lemma (in design) points_index_count_min: "multiplicity bl \<ge> n \<Longrightarrow> ps \<subseteq> bl \<Longrightarrow> points_index \<B> ps \<ge> n"
  using points_index_alt_def set_count_size_min by (metis filter_mset.rep_eq) 

lemma point_index_distrib: "points_index (B1 + B2) ps = points_index B1 ps + points_index B2 ps"
  by (simp add: points_index_def)

lemma point_index_diff: "points_index B1 ps = points_index (B1 + B2) ps - points_index B2 ps"
  by (simp add: points_index_def)

lemma points_index_singleton: "points_index {#b#} ps = 1 \<longleftrightarrow> ps \<subseteq> b"
  by (simp add: points_index_def)

lemma points_index_sum: 
  assumes "ps \<noteq> {}"
  shows "points_index (\<Sum>\<^sub>#  B ) ps = (\<Sum>b \<in># B . (points_index b ps))"
  apply (induction B)
  using points_index_empty by (auto simp add: point_index_distrib)

lemma points_index_block_image_add_eq: 
  assumes "x \<notin> ps"
  assumes "points_index B ps = l"
  shows "points_index {# insert x b . b \<in># B#} ps = l"
  apply (simp add: points_index_def)
  by (metis (no_types, lifting) assms filter_mset_cong image_mset_filter_swap2 points_index_def size_image_mset subset_insert)

lemma points_index_on_set_def [simp]: 
  assumes "finite B"
  shows "points_index (mset_set B) ps = card {b \<in> B. ps \<subseteq> b}"
  by (simp add: points_index_def assms)

lemma points_index_single_rep_num: "points_index B {x} = B rep x"
  by (simp add: points_index_def point_replication_number_def)

lemma points_index_pair_rep_num: 
  assumes "\<And> b. b \<in># B \<Longrightarrow> x \<in> b"
  assumes "ps = {x, y}"
  shows "points_index B ps = B rep y"
  apply (simp add: point_replication_number_def points_index_def)
  by (metis assms(1) assms(2) empty_subsetI filter_mset_cong insert_subset)

lemma points_index_0_left: 
  assumes "points_index B ps = 0"
  assumes "b \<in># B"
  shows "\<not> (ps \<subseteq> b)"
proof (rule ccontr)
  assume "\<not> \<not> ps \<subseteq> b"
  then have a: "ps \<subseteq> b" by auto
  then have "b \<in># {#bl \<in># B . ps \<subseteq> bl#}"
    by (simp add: assms(2)) 
  thus False
    by (metis assms(1) count_greater_eq_Suc_zero_iff count_size_set_repr not_less_eq_eq points_index_def size_filter_mset_lesseq) 
qed

lemma points_index_0_right: 
  assumes "\<And> b . b \<in># B \<Longrightarrow> (\<not> ps \<subseteq> b)"
  shows "points_index B ps = 0"
  using assms by (simp add: filter_mset_empty_conv points_index_def)

lemma points_index_0_iff: "points_index B ps = 0 \<longleftrightarrow> (\<forall> b. b \<in># B \<longrightarrow> (\<not> ps \<subseteq> b))"
  using points_index_0_left points_index_0_right by metis

lemma points_index_gt0_impl_existance: 
  assumes "points_index B ps > 0"
  shows "(\<exists> bl . (bl \<in># B \<and> ps \<subseteq> bl))"
proof -
  have "size {#bl \<in># B . ps \<subseteq> bl#} > 0"
    by (metis assms points_index_def)
  then obtain bl where "bl \<in># B" and "ps \<subseteq> bl"
    by (metis filter_mset_empty_conv nonempty_has_size) 
  thus ?thesis by auto
qed

lemma points_index_one_unique: 
  assumes "points_index B ps = 1"
  assumes "bl \<in># B" and "ps \<subseteq> bl" and "bl' \<in># B" and "ps \<subseteq> bl'"
  shows "bl = bl'"
proof (rule ccontr)
  assume assm: "bl \<noteq> bl'"
  then have bl1: "bl \<in># {#bl \<in># B . ps \<subseteq> bl#}" using assms by simp
  then have bl2: "bl'\<in># {#bl \<in># B . ps \<subseteq> bl#}" using assms by simp
  then have "{#bl, bl'#} \<subseteq># {#bl \<in># B . ps \<subseteq> bl#}" using assms
    by (metis bl1 bl2 add_mset_subseteq_single_iff assm mset_subset_eq_single points_index_def size_single subseteq_mset_size_eql) 
  then have "size {#bl \<in># B . ps \<subseteq> bl#} \<ge> 2" using size_mset_mono by fastforce 
  thus False using assms
    by (metis numeral_le_one_iff points_index_def semiring_norm(69))
qed

lemma points_index_one_unique_block: 
  assumes "points_index B ps = 1"
  shows "\<exists>! bl . (bl \<in># B \<and> ps \<subseteq> bl)"
  using assms points_index_gt0_impl_existance points_index_one_unique
  by (metis zero_less_one) 

lemma points_index_one_not_unique_block: 
  assumes "points_index B ps = 1"
  assumes "ps \<subseteq> bl"
  assumes "bl \<in># B"
  assumes "bl' \<in># B - {#bl#}"
  shows "\<not> ps \<subseteq> bl'"
proof - 
  have "B = (B - {#bl#}) + {#bl#}"
    by (simp add: assms(3)) 
  then have "points_index (B - {#bl#}) ps = points_index B ps - points_index {#bl#} ps"
    by (metis point_index_diff) 
  then have "points_index (B - {#bl#}) ps = 0" using assms points_index_singleton
    by (metis diff_self_eq_0) 
  thus ?thesis
    using assms(4) points_index_0_left by auto
qed

subsubsection \<open>Intersection Number\<close>

text \<open> The intersection number of two blocks is the size of the intersection of those blocks. i.e. 
the number of points which occur in both blocks \<close>
definition intersection_number :: "'a set \<Rightarrow> 'a set \<Rightarrow> int" where
"intersection_number b1 b2 \<equiv> card (b1 \<inter> b2)"

lemma intersection_num_non_neg: "intersection_number b1 b2 \<ge> 0"
  by (simp add: intersection_number_def)

lemma intersection_number_empty_iff: 
  assumes "finite b1"
  shows "b1 \<inter> b2 = {} \<longleftrightarrow> intersection_number b1 b2 = 0"
  by (simp add: intersection_number_def assms)

lemma intersect_num_commute: "intersection_number b1 b2 = intersection_number b2 b1"
  by (simp add: inf_commute intersection_number_def) 

definition n_intersect_number :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> int" where
"n_intersect_number b1 b2 n \<equiv> card { x \<in> Pow (b1 \<inter> b2) . card x = n}"

lemma n_intersect_num_subset_def: "n_intersect_number b1 b2 n = card {x . x \<subseteq> b1 \<inter> b2 \<and> card x = n}"
  using n_intersect_number_def by auto

lemma (in design) n_inter_num_zero: assumes "b1 \<in># \<B>" and "b2 \<in># \<B>"
  shows "n_intersect_number b1 b2 0 = 1"
proof -
  have empty: "\<And>x . finite x \<Longrightarrow> card x = 0 \<Longrightarrow> x = {}"
    by simp
  have "finite (b1 \<inter> b2)" using finite_blocks assms by simp
  then have "\<And> x . x \<in> Pow (b1 \<inter> b2) \<Longrightarrow> finite x"
    by (meson PowD finite_subset) 
  then have "card {x \<in> Pow (b1 \<inter> b2) . card x = 0} = card {{}}"  using empty
    by (smt Collect_cong Pow_bottom card_Suc_eq card_eq_0_iff insert_absorb insert_not_empty singleton_conv) (* LONG *)
  thus ?thesis by (simp add: n_intersect_number_def)
qed

lemma n_inter_num_one: "finite b1 \<Longrightarrow> finite b2 \<Longrightarrow> n_intersect_number b1 b2 1 = intersection_number b1 b2"
  using n_intersect_number_def intersection_number_def card_Pow_filter_one
  by (metis (full_types) finite_Int) 

lemma n_inter_num_choose: "finite b1 \<Longrightarrow> finite b2 \<Longrightarrow> n_intersect_number b1 b2 n =  (card (b1 \<inter> b2) choose n)" 
  using n_subsets n_intersect_num_subset_def
  by (metis (full_types) finite_Int) 

lemma (in design) n_inter_num_choose_design: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># \<B> \<Longrightarrow> n_intersect_number b1 b2 n =  (card (b1 \<inter> b2) choose n) "
  using finite_blocks by (simp add: n_inter_num_choose)

lemma (in design) n_inter_num_choose_design_inter: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># \<B> \<Longrightarrow> n_intersect_number b1 b2 n =  (nat (intersection_number b1 b2) choose n) "
  using finite_blocks by (simp add: n_inter_num_choose intersection_number_def)

(* Incidence System properties *)
context incidence_system
begin

definition replication_numbers :: "int set" where
"replication_numbers \<equiv> { point_replication_number \<B> x | x . x \<in> \<V>}"

subsubsection \<open> Block Sizes \<close>

text \<open> Enable reasoning over collection of block sizes\<close>

definition sys_block_sizes :: "int set" where
"sys_block_sizes \<equiv> { (int (card bl)) | bl. bl \<in># \<B>}"
  
lemma block_sizes_non_empty: 
  assumes "\<B> \<noteq> {#}"
  shows "card (sys_block_sizes) > 0"
proof -
  obtain bl where bl_in: "bl \<in># \<B>" using block_set_nempty_imp_block_ex assms by auto
  have def: "sys_block_sizes  = set_mset (image_mset (\<lambda> bl . int (card bl)) \<B>)"
    using sys_block_sizes_def by auto  
  have "size (image_mset (\<lambda> bl . card bl) \<B>) > 0" using bl_in
    using assms nonempty_has_size by auto  
  thus ?thesis using  def mset_size_ne0_set_card
    by (metis size_image_mset) 
qed

lemma sys_block_sizes_in: "bl \<in># \<B> \<Longrightarrow> card bl \<in> sys_block_sizes"
  unfolding sys_block_sizes_def by auto 

lemma sys_block_sizes_obtain_bl: "x \<in> sys_block_sizes  \<Longrightarrow> (\<exists> bl \<in># \<B>. int (card bl) = x)"
  by (auto simp add: sys_block_sizes_def)

definition intersection_numbers :: " int set" where
"intersection_numbers \<equiv> { intersection_number b1 b2 | b1 b2 . b1 \<in># \<B> \<and> b2 \<in># (\<B> - {#b1#})}"

(* Set of point indices *)
definition point_indices :: "int \<Rightarrow> int set" where
"point_indices t \<equiv> { points_index \<B> ps | ps. int (card ps) = t \<and> ps \<subseteq> \<V>}"

lemma point_indices_elem_in: "ps \<subseteq> \<V> \<Longrightarrow> card ps = t \<Longrightarrow> points_index \<B> ps \<in> point_indices t"
  by (auto simp add: point_indices_def)

lemma point_indices_alt_def: "point_indices t = { points_index \<B> ps | ps. int (card ps) = t \<and> ps \<subseteq> \<V>}"
  by (simp add: point_indices_def)

end

subsection \<open>Operations on designs\<close>

text \<open>This defines some of the most common operations on a design often used for constructing new designs
from old ones. In particular, many of these operations overlap with what computational tools on designs define \<close>

subsubsection \<open>Design Complements \<close>

context incidence_system
begin

text \<open> The complement of a block are all the points in the design not in that block. The complement of a design
is therefore the original point sets, and set of all block complements \<close>
abbreviation block_complement:: "'a set \<Rightarrow> 'a set" where
"block_complement b \<equiv> \<V> - b"

definition complement_blocks :: "'a set multiset" where
"complement_blocks \<equiv> {# block_complement bl . bl \<in># \<B> #}"

definition complement :: "'a set_system" where
"complement \<equiv> (\<V>, complement_blocks)"

lemma complement_order_eq [simp]: "order (complement) = card \<V>"
  by (simp add: complement_def)

lemma complement_points_eq [simp]: "points (complement) = \<V>"
  by (simp add: complement_def)

lemma complement_blocks_eq [simp]: "blocks (complement) = complement_blocks"
  by (simp add: complement_def)

lemma (in finite_incidence_system) block_complement_size: "b \<subseteq> \<V> \<Longrightarrow> card (block_complement b) = card \<V> - card b"
  by (simp add: card_Diff_subset finite_subset card_mono of_nat_diff finite_sets)  

lemma complement_same_b [simp]: "size (complement_blocks) = size \<B>"
  by (simp add: complement_blocks_def)

lemma block_complement_elem_iff: 
  assumes "ps \<subseteq> \<V>"
  shows "ps \<subseteq> (block_complement bl) \<longleftrightarrow> (\<forall> x \<in> ps. x \<notin> bl)"
  using assms by (auto)

lemma block_comp_elem_alt_left: "x \<in> bl \<Longrightarrow> ps \<subseteq> (block_complement bl) \<Longrightarrow> x \<notin> ps"
  by (auto simp add: block_complement_elem_iff)

lemma block_comp_elem_alt_right: "ps \<subseteq> \<V> \<Longrightarrow> (\<And> x . x \<in> ps \<Longrightarrow> x \<notin> bl) \<Longrightarrow> ps \<subseteq> (block_complement bl)"
  by (auto simp add: block_complement_elem_iff)

lemma (in finite_incidence_system) block_comp_incomplete: "bl \<subseteq> \<V> \<Longrightarrow> incomplete_block bl \<Longrightarrow> card (block_complement bl) > 0"
  using block_complement_size by (simp)

lemma (in finite_incidence_system) block_comp_incomplete_nempty: "bl \<subseteq> \<V> \<Longrightarrow> incomplete_block bl \<Longrightarrow>(block_complement bl) \<noteq> {}"
  by (auto simp add: block_complement_size block_comp_incomplete)

lemma (in finite_incidence_system) incomplete_block_proper_subset: "bl \<subseteq> \<V> \<Longrightarrow> incomplete_block bl \<Longrightarrow> bl \<subset> \<V>"
  by auto 

lemma (in design) des_complement_rep_number: 
  assumes "x \<in> \<V>" and "\<B> rep x = r" shows  "(complement_blocks) rep x = \<b> - r"
proof - 
  have r: "size {#b \<in># \<B> . x \<in> b#} = r" using assms by (simp add: point_replication_number_def)
  then have a: "\<And> b . b \<in># \<B> \<Longrightarrow> x \<in> b \<Longrightarrow> x \<notin> block_complement b"
    by simp  
  have "\<And> b . b \<in># \<B> \<Longrightarrow> x \<notin> b \<Longrightarrow> x \<in> block_complement b"
    by (simp add: assms(1)) 
  then have alt: "(image_mset block_complement \<B>) rep x = size {#b \<in># \<B> . x \<notin> b#}" using a
    by (smt (verit, ccfv_SIG) filter_mset_cong image_mset_filter_swap2 point_replication_number_def size_image_mset) 
  have "\<b> = size {#b \<in># \<B> . x \<in> b#} + size {#b \<in># \<B> . x \<notin> b#}"
    by (metis multiset_partition size_union) 
  thus ?thesis using alt
    by (simp add: r complement_blocks_def)
qed

lemma complement_index:
  assumes "ps \<subseteq> \<V>"
  shows "points_index (complement_blocks) ps = size {# b \<in># \<B> . (\<forall> x \<in> ps . x \<notin> b) #}"
proof -
  have "points_index (complement_blocks) ps =  size {# b \<in># {# block_complement bl . bl \<in># \<B>#}. ps \<subseteq> b #}"
    by (simp add: complement_blocks_def points_index_def) 
  then have "points_index (complement_blocks) ps = size {# block_complement bl | bl \<in># \<B> . ps \<subseteq> (block_complement bl)#}"
    by (metis image_mset_filter_swap)
  thus ?thesis using assms by (simp add: block_complement_elem_iff complement_def)
qed

lemma complement_index_2:
  assumes "{x, y} \<subseteq> \<V>"
  shows "points_index (complement_blocks) {x, y} = size {# b \<in># \<B> . x \<notin> b \<and> y \<notin> b #}"
proof -
  have a: "\<And> b. b \<in># \<B> \<Longrightarrow> \<forall> x' \<in> {x, y} . x' \<notin> b \<Longrightarrow> x \<notin> b \<and> y \<notin> b"
    by simp 
  have "\<And> b. b \<in># \<B> \<Longrightarrow> x \<notin> b \<and> y \<notin> b \<Longrightarrow> \<forall> x' \<in> {x, y} . x' \<notin> b "
    by simp 
  thus ?thesis using assms a complement_index
    by (smt (verit) filter_mset_cong) 
qed

lemma (in incidence_system) complement_wf [intro]: "incidence_system \<V> (complement_blocks)"
  using wellformed by (unfold_locales) (auto simp add: complement_blocks_def)

lemma (in finite_incidence_system) complement_finite: "finite_incidence_system \<V> ((complement_blocks))"
  using complement_wf finite_sets by (simp add: incidence_system.finite_sysI) 

lemma (in design) complement_design: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> incomplete_block bl" 
  shows "design \<V> (complement_blocks)"
proof -
  interpret fin: finite_incidence_system \<V> "complement_blocks" using complement_finite by simp
  show ?thesis using assms block_comp_incomplete_nempty wellformed by (unfold_locales) (auto simp add: complement_blocks_def)
qed

subsubsection \<open>Multiples\<close>
text \<open>An easy way to construct new set systems is to simply multiply the block collection by some constant \<close>

abbreviation multiple_blocks :: "nat \<Rightarrow> 'a set multiset" where
"multiple_blocks n \<equiv> repeat_mset n \<B>"

definition multiple :: "nat \<Rightarrow> 'a set_system" where 
"multiple n \<equiv> (\<V>, multiple_blocks n)"

lemma multiple_order_constant [simp]: "card \<V> = card (points (multiple n))"
  by (simp add: multiple_def)

lemma multiple_points_same [simp]: "points (multiple n) = \<V>"
  by (simp add: multiple_def)

lemma multiple_blocks_simp [simp]: "blocks (multiple n) = multiple_blocks n"
  by (simp add: multiple_def)

lemma (in design) multiple_order [simp]: "order (multiple n) = \<v>"
  by (simp add: multiple_def)

lemma multiple_block_in_original: "b \<in># multiple_blocks n \<Longrightarrow> b \<in># \<B>"
  by (simp add: elem_in_repeat_in_original) 

lemma multiple_block_in: "n > 0 \<Longrightarrow> b \<in># \<B> \<Longrightarrow>  b \<in># multiple_blocks n"
  by (simp add: elem_in_original_in_repeat)

lemma (in design) multiple_blocks_num [simp]: "size (multiple_blocks n) = n*\<b>"
  by simp

lemma multiple_blocks_gt: "n > 0 \<Longrightarrow> size (multiple_blocks n) \<ge> size \<B>" 
  by (simp)

lemma block_original_count_le: "n > 0 \<Longrightarrow> count \<B> b \<le> count (multiple_blocks n) b"
  using count_repeat_mset by simp 

lemma multiple_blocks_sub: "n > 0 \<Longrightarrow> \<B> \<subseteq># (multiple_blocks n)"
  by (simp add: mset_subset_eqI block_original_count_le) 

lemma multiple_1_same: "multiple 1 = (\<V>, \<B>)"
  unfolding multiple_def by simp

lemma multiple_unfold_1: "multiple (Suc n) = (\<V>, (multiple_blocks n) + \<B>)"
  unfolding multiple_def by simp

lemma multiple_point_rep_num: "x \<in> V \<Longrightarrow> blocks (multiple n) rep x = (\<B> rep x) * n"
proof (induction n)
  case 0
  then show ?case by (simp add: point_replication_number_def multiple_def)
next
  case (Suc n)
  then have "multiple_blocks (Suc n) rep x = \<B> rep x * n + (\<B> rep x)"
    using Suc.IH Suc.prems by (simp add: multiple_def union_commute point_replication_number_def)
  then show ?case
    by (simp add: int_distrib(2) multiple_def) 
qed

lemma multiple_point_rep_num_incidence: "x \<in> \<V> \<Longrightarrow> (multiple_blocks n) rep x = (\<B> rep x) * n"
  using multiple_point_rep_num by simp 

lemma multiple_point_index: 
  assumes "ps \<subseteq> \<V>"
  shows "points_index (multiple_blocks n) ps = (points_index \<B> ps) * n"
  by (induction n) (auto simp add: points_index_def)

lemma repeat_mset_block_point_rel: "\<And>b x. b \<in># multiple_blocks  n \<Longrightarrow> x \<in> b \<Longrightarrow> x \<in> \<V>"
  apply (induction n)
   apply (auto)
  by (meson subset_iff wellformed)

lemma multiple_is_wellformed: "incidence_system \<V> (multiple_blocks n)"
  using repeat_mset_subset_in wellformed repeat_mset_block_point_rel by (unfold_locales) (auto)

lemma (in finite_incidence_system) multiple_is_finite: "finite_incidence_system \<V> (multiple_blocks n)"
  using multiple_is_wellformed finite_sets by (unfold_locales) (auto simp add: incidence_system_def)

lemma (in design) multiple_is_design:
  assumes "n > 0"
  shows "design \<V> (multiple_blocks n)"
proof -
  interpret fis: finite_incidence_system \<V> "multiple_blocks n" using multiple_is_finite by simp
  show ?thesis using assms
    by (unfold_locales) (auto simp add: blocks_nempty elem_in_repeat_in_original repeat_mset_not_empty)
qed

interpretation mult_sys: incidence_system \<V> "(multiple_blocks n)"
  by (simp add: multiple_is_wellformed)

lemma multiple_block_multiplicity [simp]: "mult_sys.multiplicity n bl = (multiplicity bl) * n"
  by (simp add: multiple_def) 

lemma multiple_block_sizes_same: 
  assumes "n > 0" 
  shows "sys_block_sizes = mult_sys.sys_block_sizes n"
proof -
  have def: "mult_sys.sys_block_sizes n = {card bl | bl. bl \<in># (multiple_blocks n)}"
    by (simp add: mult_sys.sys_block_sizes_def) 
  then have eq: "\<And> bl. bl \<in># (multiple_blocks n) \<longleftrightarrow> bl \<in># \<B>"
    using assms multiple_block_in multiple_block_in_original by blast 
  thus ?thesis using def by (simp add: sys_block_sizes_def eq)
qed 

subsubsection \<open>Combining Set Systems \<close>
text \<open>Similar to multiple, another way to construct a new set system is to combine two existing ones \<close>

definition combine :: "'a set \<Rightarrow> 'a set multiset \<Rightarrow> 'a set_system" where
"combine V B \<equiv> (\<V> \<union> V, \<B> + B)"

lemma combine_points_simp [simp]: "points (combine V B) = \<V> \<union> V"
  by (simp add: combine_def)

lemma combine_blocks_simp [simp]: "blocks (combine V B ) = \<B> + B"
  by (simp add: combine_def)

lemma combine_same_points: "V1 = \<V> \<Longrightarrow> combine V1 B1 = (\<V>, B1 + \<B>)"
  by (simp add: combine_def)

lemma combine_points_index:
  assumes "ps \<subseteq> \<V>"
  shows "points_index (B + \<B>) ps = points_index B ps  + points_index \<B> ps"
  by (simp add: points_index_def combine_def)

lemma combine_multiple: "combine \<V> \<B> = multiple 2"
  unfolding multiple_def combine_def 
  by auto

lemma (in finite_incidence_system) combine_order: "finite_incidence_system V' B' \<Longrightarrow> order (combine V' B') \<ge> card \<V>"
  by (simp add:finite_sets combine_def finite_incidence_system.finite_sets card_mono)

lemma (in finite_incidence_system) combine_order_2: "finite_incidence_system V' B' \<Longrightarrow> order (combine V' B') \<ge> card V'"
  by (simp add: card_mono combine_def finite_sets finite_incidence_system.finite_sets) 

lemma combine_rep_number: "(\<B> + B') rep x = \<B> rep x + B' rep x"
  by (simp add: point_replication_number_def)

lemma combine_points_in_or: "x \<in> points (combine V' B') \<Longrightarrow> x \<in> \<V> \<or> x \<in> V'"
  by (simp)

lemma combine_point_index: "points_index (\<B> + B') x = points_index \<B> x + points_index B' x"
  by (simp add: points_index_def combine_def)

lemma combine_multiplicity: "count (blocks (combine V B)) b = multiplicity b + count B b"
  by (auto simp add: combine_def)
(*
lemma combine_block_sizes: "sys_block_sizes (combine D D2) = sys_block_sizes D \<union> sys_block_sizes D2"
  by (auto simp add: combine_def sys_block_sizes_def)
*)
lemma combine_incidence_systems: "incidence_system V' B' \<Longrightarrow> incidence_system (\<V> \<union> V') (\<B> + B')"
   using incidence_system_def wellformed by (unfold_locales) auto

lemma (in finite_incidence_system) combine_finite_systems: "finite_incidence_system V' B' \<Longrightarrow> finite_incidence_system (\<V> \<union> V') (\<B> + B')"
  apply (intro_locales)
   apply (simp add: combine_incidence_systems finite_incidence_system.axioms(1)) 
  by (simp add: combine_def finite_incidence_system_axioms_def finite_incidence_system_def finite_sets) 

lemma (in design) combine_designs: 
  assumes "design V' B'"
  shows "design (\<V> \<union> V') (\<B> + B')"
proof -
  interpret fin: finite_incidence_system "(\<V> \<union> V')" "(\<B> + B')"
    by (simp add: assms(1) combine_finite_systems design.axioms(1))
  show ?thesis using assms design.wf_design_iff blocks_nempty
    by(unfold_locales, simp_all, blast)
qed

end
subsubsection \<open>Add and Delete Points/Blocks \<close>
text \<open> Computational tools for designs such as the GAP library define the idea of adding/removing 
blocks and points from a design for investigative purposes. These definitions also closely align with 
hypergraph theory, a structure closely related to designs \<close>

context incidence_system
begin

definition add_point :: "'a \<Rightarrow> 'a set_system" where
"add_point p \<equiv> ((insert p \<V>), \<B>)"

lemma add_point_points [simp]: "points (add_point p) = (insert p \<V>)"
  by (simp add: add_point_def)

lemma add_point_blocks_simp [simp]: "blocks (add_point p) = \<B>"
  by (simp add: add_point_def)

lemma add_existing_point: "p \<in> \<V> \<Longrightarrow> add_point p = (\<V>, \<B>)"
  using add_point_def by fastforce

lemma add_point_wf: "incidence_system (insert p \<V>) \<B>"
  using wf_invalid_point by (unfold_locales) (auto)

lemma (in finite_incidence_system) add_point_finite: "finite_incidence_system (insert p \<V>) \<B>"
  using add_point_wf finite_sets by (unfold_locales) (simp_all add: incidence_system_def)

lemma (in design) add_point_design: "design (insert p \<V>) \<B>"
  using add_point_wf finite_sets blocks_nempty 
  by (unfold_locales) (auto simp add: incidence_system_def)

definition add_point_to_blocks :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set_system" where
"add_point_to_blocks p bs \<equiv> ((insert p \<V>), {# (insert p b) | b \<in># \<B> . b \<in> bs#} + {# b \<in># \<B> . b \<notin> bs#})"

lemma add_point_blocks_points [simp]: "points (add_point_to_blocks p bs) = (insert p \<V>)"
  by (simp add: add_point_to_blocks_def)

lemma add_point_blocks_blocks [simp]: "blocks (add_point_to_blocks p bs) = {# (insert p b) | b \<in># \<B> . b \<in> bs#} + {# b \<in># \<B> . b \<notin> bs#}"
  by (simp add: add_point_to_blocks_def)

lemma add_point_blocks_blocks_alt: "blocks (add_point_to_blocks p bs) = image_mset (insert p) (filter_mset (\<lambda> b . b \<in> bs) \<B>) + (filter_mset (\<lambda> b . b \<notin> bs) \<B>)"
  by simp


lemma add_point_blocks_eq [simp]: "add_point_to_blocks p {} = add_point p"
  by (simp add: add_point_def add_point_to_blocks_def)

lemma add_point_blocks_point_eq: "points (add_point_to_blocks p bs) = points (add_point p)"
  by simp

lemma add_point_existing_blocks: assumes "(\<And> bl . bl \<in> bs \<Longrightarrow> p \<in> bl)" shows "blocks (add_point_to_blocks p bs) = \<B>"
proof (simp add: add_point_to_blocks_def)
  have "image_mset (insert p) {#b \<in># \<B>. b \<in> bs#} = {#b \<in># \<B>. b \<in> bs#}" using assms
    by (simp add: image_filter_cong insert_absorb) 
  thus "image_mset (insert p) {#b \<in># \<B>. b \<in> bs#} + {#b \<in># \<B>. b \<notin> bs#} = \<B>"  using multiset_partition
    by simp 
qed

definition delete_point :: "'a \<Rightarrow> 'a set_system" where
"delete_point p \<equiv> (\<V> - {p}, {# (bl - {p}) . bl \<in># \<B> #})" (* As defined in GAP library/weak deletion in hypergraph theory *)

lemma delete_point_points [simp]: "points (delete_point p) = \<V> - {p}"
  by (simp add: delete_point_def)

lemma delete_point_blocks [simp]: "blocks (delete_point p) = {# (bl - {p}) . bl \<in># \<B> #}"
  by (simp add: delete_point_def)

lemma delete_point_block_count: "size (blocks (delete_point p)) = size \<B>"
  by (simp add: delete_point_def)

lemma remove_invalid_point_block: "p \<notin> \<V> \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> bl - {p} = bl"
  using wf_invalid_point by blast

lemma delete_point_p_not_in_points: "p \<notin> \<V> \<Longrightarrow> points (delete_point p) = \<V>"
  by (simp)

lemma delete_point_p_not_in_blocks: "p \<notin> \<V> \<Longrightarrow> blocks (delete_point p) = \<B>"
  using delete_point_p_not_in_points
  by (auto simp add: remove_invalid_point_block) 

lemma delete_point_p_not_in_bl_blocks: "(\<And> bl. bl \<in># \<B> \<Longrightarrow> p \<notin> bl) \<Longrightarrow> blocks (delete_point p) = \<B>"
  by simp

lemma delete_invalid_point_eq: assumes "p \<notin> \<V>" 
  shows "delete_point p = (\<V>, \<B>)"
proof -
  have v_eq: "\<V> - {p} = \<V>"
    by (simp add: assms) 
  have "{# (bl - {p}) . bl \<in># \<B> #} = \<B>"
    by (simp add: assms remove_invalid_point_block) 
  thus ?thesis
    by (metis v_eq assms delete_point_p_not_in_blocks delete_point_points prod.collapse) 
qed

lemma delete_point_blocks_wf: "b \<in># blocks (delete_point p) \<Longrightarrow> b \<subseteq> \<V> - {p}"
  unfolding delete_point_def using wellformed by auto

lemma delete_point_blocks_sub: 
  assumes "b \<in># blocks (delete_point p)" 
  obtains bl where "bl \<in># \<B> \<and> b \<subseteq> bl"
  using assms by (auto simp add: delete_point_def)

lemma delete_point_split_blocks: "blocks (delete_point p) = {# bl \<in>#\<B> . p \<notin> bl#} + {# bl - {p} | bl \<in># \<B> . p \<in> bl#}"
proof -
  have sm: "\<And> bl . p \<notin> bl \<Longrightarrow> bl - {p} = bl" by simp 
  have "blocks (delete_point p) = {# (bl - {p}) . bl \<in># \<B> #}" by simp
  also have "... = {# (bl - {p}) | bl \<in># \<B> . p \<notin> bl #} + {# (bl - {p}) | bl \<in># \<B> . p \<in> bl #}"
    using multiset_partition by (metis image_mset_union union_commute) 
  finally have "blocks (delete_point p) = {#bl | bl \<in># \<B> . p \<notin> bl#} + {# (bl - {p}) | bl \<in># \<B> . p \<in> bl #}"
    using sm by (metis (mono_tags, lifting) Multiset.set_mset_filter mem_Collect_eq multiset.map_cong) 
  thus ?thesis by simp
qed

lemma delete_point_index_eq: assumes "ps \<subseteq> (points (delete_point p))"
  shows "points_index (blocks (delete_point p)) ps = points_index \<B> ps"
proof -
  have eq: "filter_mset ((\<subseteq>) ps) {#bl - {p}. bl \<in># \<B>#} = image_mset (\<lambda> b . b - {p}) (filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)"
    using filter_mset_image_mset by blast
  have "p \<notin> ps" using assms by auto
  then have "\<And> bl . ps \<subseteq> bl \<longleftrightarrow> ps \<subseteq> bl - {p}" by blast
  then have "((filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)) = (filter_mset (\<lambda> b . ps \<subseteq> b) \<B>)" by auto 
  then have "size (image_mset (\<lambda> b . b - {p}) (filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)) = points_index \<B> ps" 
    by (simp add: points_index_def) 
  thus ?thesis using eq by (simp add: points_index_def)
qed

lemma delete_point_wf: "incidence_system (points (delete_point p)) (blocks (delete_point p))"
  using delete_point_blocks_wf by(unfold_locales) auto

lemma (in finite_incidence_system) delete_point_finite: "finite_incidence_system (points (delete_point p)) (blocks (delete_point p))"
  using finite_sets delete_point_wf  by (unfold_locales) (simp_all add: incidence_system_def delete_point_def)

lemma (in design) delete_point_design: 
  assumes "(\<And> bl . bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> card bl \<ge> 2)"
  shows "design (points (delete_point p)) (blocks (delete_point p))"
proof (cases "p \<in> \<V>")
  case True
  interpret fis: finite_incidence_system "(points (delete_point p))" "(blocks (delete_point p))" 
    using delete_point_finite by simp
  show ?thesis 
  proof (unfold_locales)
    show "\<And>bl. bl \<in># blocks (delete_point p) \<Longrightarrow> bl \<noteq> {}" using assms delete_point_def 
    proof -
      fix bl 
      assume "bl \<in>#blocks (delete_point p)"
      then obtain bl' where block: "bl' \<in># \<B>" and rem: "bl = bl' - {p}" by (auto simp add: delete_point_def)
      then have eq: "p \<notin> bl' \<Longrightarrow> bl \<noteq> {}" using block blocks_nempty by (simp add: rem) 
      have "p \<in> bl' \<Longrightarrow> card bl \<ge> 1" using rem finite_blocks block assms block by fastforce  
      then show "bl \<noteq> {}" using  eq assms by fastforce 
    qed 
  qed
next
  case False
  then show ?thesis using delete_invalid_point_eq
    by (simp add: wf_design) 
qed

definition strong_delete_point :: "'a \<Rightarrow> 'a set_system" where (* Hypergraph theory concept *)
"strong_delete_point p \<equiv> (\<V> - {p}, {# bl \<in># \<B> . p \<notin> bl#})"

lemma strong_delete_point_points [simp]: "points (strong_delete_point p) = \<V> - {p}"  
  by (simp add: strong_delete_point_def)

lemma strong_delete_point_blocks [simp] : "blocks (strong_delete_point p) = {# bl \<in># \<B> . p \<notin> bl#}"  
  by (simp add: strong_delete_point_def)

lemma strong_delete_point_blocks_alt: "blocks (strong_delete_point p) = \<B> - {# bl \<in># \<B> . p \<in> bl#}"  
  using  add_diff_cancel_left' multiset_partition by (metis strong_delete_point_blocks) 

lemma delete_point_strong_eq: "points (delete_point p) = points (strong_delete_point p)"
  by (simp add: delete_point_def strong_delete_point_def)

lemma delete_point_strong_block_in:  "p \<notin> bl \<Longrightarrow> bl \<in># \<B>  \<Longrightarrow> bl \<in># blocks (strong_delete_point p)"
  by simp

lemma delete_point_strong_block_not_in:
  assumes "p \<in> bl"
  shows "bl \<notin># blocks (strong_delete_point p)"
  using assms by simp

lemma (in finite_incidence_system) strong_del_point_order: "p \<in> \<V> \<Longrightarrow> order (strong_delete_point p) = \<v> - 1"
  using finite_sets
  by (metis Diff_cancel block_comp_elem_alt_left card_0_eq card_Diff_singleton diff_is_0_eq' int_ops(2) less_one nat_le_linear nat_neq_iff of_nat_diff strong_delete_point_points subset_empty zero_less_diff) 

lemma delete_point_strong_block_in_iff:
  assumes "bl \<in># \<B>"
  shows "bl \<in># blocks (strong_delete_point p) \<longleftrightarrow> p \<notin> bl"
  by (simp add: delete_point_strong_block_in delete_point_strong_block_not_in assms)

lemma delete_point_strong_block_subset: "blocks (strong_delete_point p) \<subseteq># \<B>"
  by (simp add: strong_delete_point_def)

lemma delete_point_strong_block_in_orig: "bl \<in># blocks (strong_delete_point p) \<Longrightarrow> bl \<in># \<B>"
  using delete_point_strong_block_subset by (metis mset_subset_eqD) 

lemma delete_invalid_pt_strong_eq: "p \<notin> \<V> \<Longrightarrow> (\<V>, \<B>) = strong_delete_point p"
proof (intro prod_eqI)
  show "p \<notin> \<V> \<Longrightarrow> points (\<V>, \<B>) = points (strong_delete_point p)"
    by (metis delete_invalid_point_eq delete_point_strong_eq)
next 
  assume "p \<notin> \<V>"
  then have "{# bl \<in># \<B>. p \<notin> bl#} = \<B>"
    by (simp add: filter_mset_eq_conv wf_invalid_point)  
  thus "blocks (\<V>, \<B>) = blocks (strong_delete_point p)" by (simp add: strong_delete_point_def)
qed

lemma strong_del_point_index_alt: assumes "ps \<subseteq> (points (strong_delete_point p))"
  shows "points_index (blocks (strong_delete_point p)) ps = points_index \<B> ps - points_index {# bl \<in># \<B> . p \<in> bl#} ps"
  by (metis filter_diff_mset incidence_system.strong_delete_point_blocks_alt incidence_system_axioms multiset_filter_mono multiset_filter_subset points_index_def size_Diff_submset)

lemma strong_del_point_incidence_wf: "incidence_system (points (strong_delete_point p)) (blocks (strong_delete_point p))"
  using wellformed by(unfold_locales) auto

lemma (in finite_incidence_system) strong_del_point_finite: "finite_incidence_system (points (strong_delete_point p)) (blocks (strong_delete_point p))"
  using strong_del_point_incidence_wf by (intro_locales) (simp_all add: finite_incidence_system_axioms_def finite_sets )

lemma (in design) strong_del_point_design: "design (points (strong_delete_point p)) (blocks (strong_delete_point p))"
proof -
  interpret fin: finite_incidence_system "(points (strong_delete_point p))" "(blocks (strong_delete_point p))"
    using strong_del_point_finite by simp
  show ?thesis using wf_design wf_design_iff by (unfold_locales) (auto)
qed

definition add_block :: "'a set \<Rightarrow> 'a set_system" where (* We define add_block to allow b to not be a subset of V, but to still be closed. This is slightly different to other descriptions which are not total where the function is only defined when bs \<subseteq> \<V> *)
"add_block b \<equiv> (\<V> \<union> b, \<B> + {#b#})"

lemma add_block_points [simp]: "points (add_block b) = \<V> \<union> b"
  by (simp add: add_block_def)

lemma add_block_blocks [simp]: "blocks (add_block b) = add_mset b \<B>"
  by (simp add: add_block_def)

lemma add_wf_block_points [simp]: "bl \<subseteq> \<V> \<Longrightarrow> points (add_block bl) = \<V>"
  by (auto simp add: add_block_def)

lemma add_block_wf: "incidence_system (points (add_block b)) (blocks (add_block b))"
  using  wellformed by (unfold_locales) auto

lemma (in finite_incidence_system) add_block_fin: "finite b \<Longrightarrow> finite_incidence_system (points (add_block b)) (blocks (add_block b))"
   using wf_invalid_point finite_sets by (unfold_locales) auto

lemma (in design) add_block_design: 
  assumes "finite bl" 
  assumes "bl \<noteq> {}" 
  shows "design (points (add_block bl)) (blocks (add_block bl))"
proof - 
  interpret fin: finite_incidence_system "(points (add_block bl))" "(blocks (add_block bl))" 
    using add_block_fin assms by simp
  show ?thesis 
    using blocks_nempty assms by (unfold_locales) auto
qed

definition delete_block :: "'a set \<Rightarrow> 'a set_system" where
"delete_block b \<equiv> (\<V>, \<B> - {#b#})"

lemma delete_block_points [simp]: "points (delete_block b) = \<V>"
  by (simp add: delete_block_def)

lemma delete_block_blocks [simp]: "blocks (delete_block b) =  \<B> - {#b#}"
  by (simp add: delete_block_def)

lemma delete_block_blocks_subset: "blocks (delete_block b) \<subseteq># \<B>"
  by (simp add: delete_block_def)

lemma delete_invalid_block_eq: "b \<notin># \<B> \<Longrightarrow> delete_block b = (\<V>, \<B>)"
  by (simp add: delete_block_def)

lemma delete_block_wf: "incidence_system \<V> (\<B> - {#bl#})"
  by (unfold_locales) (simp add: in_diffD wellformed) 

lemma (in finite_incidence_system) delete_block_fin_incidence_sys: "finite_incidence_system \<V> (\<B> - {#bl#})"
   using delete_block_wf finite_sets by (unfold_locales) (simp_all add: incidence_system_def)

lemma (in design) delete_block_design:  "design \<V> (\<B> - {#bl#})"
proof -
  interpret fin: finite_incidence_system \<V> "(\<B> - {#bl#})" using delete_block_fin_incidence_sys by simp
  have "\<And> b . b \<in># (\<B> - {#bl#}) \<Longrightarrow> b \<noteq> {}"
    by (meson blocks_nempty in_diffD) 
  then show ?thesis by (unfold_locales) simp_all
qed

definition strong_delete_block :: "'a set \<Rightarrow> 'a set_system" where
"strong_delete_block b \<equiv> (\<V> - b, {# bl - b | bl \<in># \<B> . bl \<noteq> b #})"

lemma strong_del_block_points [simp]: "points (strong_delete_block b) = \<V> - b"
  by (simp add: strong_delete_block_def)

lemma strong_del_block_blocks [simp]: "blocks (strong_delete_block b) = {# bl - b | bl \<in># \<B> . bl \<noteq> b #}"
  by (simp add: strong_delete_block_def)

lemma strong_del_block_alt_blocks_def: "blocks (strong_delete_block b) = {# bl - b . bl \<in># removeAll_mset b \<B> #}"
  by (simp add: filter_mset_neq)

lemma strong_del_block_wf: "incidence_system (points (strong_delete_block b)) (blocks (strong_delete_block b))"
  using wf_invalid_point by (unfold_locales) auto

lemma (in finite_incidence_system) strong_del_block_fin: "finite_incidence_system (points (strong_delete_block b)) (blocks (strong_delete_block b))"
  using strong_del_block_wf finite_sets finite_incidence_system_axioms_def by (intro_locales) auto

lemma (in design) strong_del_block_des: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> \<not> (bl \<subset> b)"
  shows "design (points (strong_delete_block b)) (blocks (strong_delete_block b))"
proof -
  interpret fin: finite_incidence_system "(points (strong_delete_block b))" "(blocks (strong_delete_block b))"
    using strong_del_block_fin by simp
  show ?thesis using assms by (unfold_locales) auto
qed

interpretation add_point_in_sys: incidence_system "points (add_point p)" "blocks (add_point p)"
  using add_point_wf add_point_def by simp

interpretation del_point_sys: incidence_system "points (delete_point p)" "blocks (delete_point p)"
  using delete_point_wf by auto

interpretation add_block_sys: incidence_system "points (add_block bl)" "blocks (add_block bl)"
  using add_block_wf by simp

interpretation del_block_sys: incidence_system "points (delete_block bl)" "blocks (delete_block bl)"
  using delete_block_wf by simp 

lemma add_delete_point_inv: assumes "p \<notin> \<V>"
  shows "add_point_in_sys.delete_point p p = (\<V>, \<B>)"
proof -
  have "points (add_point_in_sys.delete_point p p) = (insert p \<V>) - {p}"
    using add_point_in_sys.delete_point_points by auto 
  then have p: "points (add_point_in_sys.delete_point p p) = \<V>"
    by (simp add: assms) 
  have "\<And> bl. bl \<in># blocks (add_point p) \<Longrightarrow> p \<notin> bl" using assms
    by (simp add: wf_invalid_point) 
  then have b: "blocks (add_point_in_sys.delete_point p p) = \<B>"
    using add_point_in_sys.delete_point_p_not_in_bl_blocks by auto
  thus ?thesis using p by (metis surjective_pairing) 
qed

lemma add_del_block_inv: assumes "bl \<subseteq> \<V>"
  shows "add_block_sys.delete_block bl bl = (\<V>, \<B>)"
proof -
  have p: "points (add_block_sys.delete_block bl bl ) = \<V>" using assms
    using add_block_sys.delete_block_points add_wf_block_points by blast 
  have b: "blocks (add_block_sys.delete_block bl bl) = (\<B> + {#bl#}) - {#bl#}"
    using add_block_sys.delete_block_blocks by force
  thus ?thesis
    by (metis diff_union_cancelR p prod.collapse) 
qed

lemma del_add_block_inv: "bl \<in># \<B> \<Longrightarrow> del_block_sys.add_block bl bl = (\<V>, \<B>)"
  using del_block_sys.add_block_points del_block_sys.add_block_blocks
  del_block_sys.add_block_def wellformed by fastforce


(*
lemma delete_add_inv: 
  assumes "p \<in> \<V>"
  shows "del_point_sys.add_point_to_blocks p p (set_mset {#(bl - {p}) | bl \<in># \<B> . p \<in> bl#})  = (\<V>, \<B>)" 
proof - 
  let ?bs = "set_mset {#(bl - {p}) | bl \<in># \<B> . p \<in> bl#}"
  have "points (del_point_sys.add_point_to_blocks p p ?bs) = insert p (\<V> - {p})"
    using del_point_sys.add_point_blocks_points by force 
  then have p: "points (del_point_sys.add_point_to_blocks p p ?bs) = \<V>" using assms
    by auto
  have simp_cond: "\<And> bl . bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> insert p (bl - {p}) = bl"
    by auto 
  have simp_cond2: "\<And> bl . bl \<in># \<B> \<Longrightarrow> p \<notin> bl \<Longrightarrow>(bl - {p}) = bl"
    by auto 
  have cond: "\<And> bl . bl \<in># \<B> \<Longrightarrow>  (bl - {p}) \<in> ?bs \<longleftrightarrow> p \<in> bl " 
  proof (rule iffI)
    fix bl
    assume "bl \<in># \<B>"
    assume "(bl - {p}) \<in> ?bs"
    then have "(bl - {p}) \<in># image_mset (\<lambda> b . b - {p}) {# bl \<in># \<B> . p \<in> bl#}" by simp
    then obtain bl' where "bl' - {p} = (bl - {p})" and "bl' \<in># {# bl \<in># \<B> . p \<in> bl#}"
      by fastforce

    thus "p \<in> bl" sorry
  next 
    fix bl
    assume "bl \<in># \<B>"
    assume "p \<in> bl"
    show "(bl - {p}) \<in> ?bs" 
  qed 
  have "blocks (delete_point p) = {# (bl - {p}) . bl \<in># \<B> #}" by simp
  then have bl: "blocks (del_point_sys.add_point_to_blocks p p (?bs)) = 
{# (insert p b) | b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<in> ?bs#} + {# b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<notin> ?bs#}"
    using del_point_sys.add_point_blocks_blocks by fastforce 
  have 0: "{# (insert p b) | b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<in> ?bs#} = image_mset (\<lambda> b . insert p b) (filter_mset (\<lambda> b . b \<in> ?bs) (image_mset (\<lambda> bl . bl - {p}) \<B>))"
    by auto
  also have 1: "... = image_mset (\<lambda> b . insert p b) (image_mset (\<lambda> bl . bl - {p}) (filter_mset  (\<lambda> b . (b - {p}) \<in> ?bs) \<B>))"
    by (metis (no_types, lifting) filter_mset_cong filter_mset_image_mset)
  also have 2: "... = image_mset (\<lambda> b . insert p (b - {p})) (filter_mset  (\<lambda> b . (b - {p}) \<in> ?bs) \<B>)"
    using image_image_mset by blast 
  also have 3: "... = image_mset (\<lambda> b . insert p (b - {p})) (filter_mset  (\<lambda> b . p \<in> b) \<B>)" using cond
    using filter_mset_cong by force 
  finally have "{# (insert p b) | b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<in> ?bs#} = {# insert p (b - {p}) | b \<in># \<B> . p \<in> b#}" using 0 1 2 3 by presburger
  then have b1: "{# (insert p b) | b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<in> ?bs#} = {# b \<in># \<B> . p \<in> b#}" 
    using simp_cond image_filter_cong by force 
  have "{# b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<notin> ?bs#} = {# (bl - {p}) | bl \<in># \<B> . (bl - {p}) \<notin> ?bs#}"
    using filter_mset_image_mset by simp
  then have "{# b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<notin> ?bs#} = {# (bl - {p}) | bl \<in># \<B> . p \<notin> bl #}" using cond
    by (metis (mono_tags, lifting) filter_mset_cong) 
  then have "{# b \<in># {# (bl - {p}) . bl \<in># \<B> #} . b \<notin> ?bs#} = {# bl \<in># \<B> . p \<notin> bl#}" using simp_cond2
    by (metis (mono_tags, lifting) Multiset.set_mset_filter mem_Collect_eq multiset_image_do_nothing) 
  then have "blocks (del_point_sys.add_point_to_blocks p p ?bs) = \<B>" using b1 bl by fastforce  
  thus ?thesis
    using del_point_sys.add_point_to_blocks_def p by fastforce 
qed

*)

end
subsection \<open> Simple Designs \<close>

text \<open> Simple designs are those in which the multiplicity of each block is at most one. 
In other words, the block collection is a set \<close>

locale simple_design = design + 
  assumes simple [simp]: "bl \<in># \<B> \<Longrightarrow> multiplicity bl = 1"

begin 

lemma simple_alt_def_all: "\<forall> bl \<in># \<B> . multiplicity bl = 1"
  using simple by auto
  
lemma simple_blocks_eq_sup: "mset_set (design_support) = \<B>"
  using distinct_mset_def simple by (metis distinct_mset_set_mset_ident) 

lemma simple_block_size_eq_card: "\<b> = card (design_support)"
  by (metis simple_blocks_eq_sup size_mset_set)

lemma points_index_simple_def: "points_index \<B> ps = card {b \<in> design_support . ps \<subseteq> b}"
  by (simp add: points_index_def card_size_filter_eq simple_blocks_eq_sup)

lemma replication_num_simple_def: "\<B> rep x = card {b \<in> design_support . x \<in> b}"
  by (simp add: point_replication_number_def card_size_filter_eq simple_blocks_eq_sup)

end

context incidence_system
begin
lemma simple_not_multiplicity: "b \<in># \<B> \<Longrightarrow> multiplicity  b > 1 \<Longrightarrow> \<not> simple_design \<V> \<B>"
  using simple_design_def simple_design_axioms_def by (metis nat_neq_iff) 

lemma multiple_not_simple: 
  assumes "n > 1"
  assumes "\<B> \<noteq> {#}"
  shows "\<not> simple_design \<V> (multiple_blocks n)"
proof (rule ccontr, simp)
  assume "simple_design \<V> (multiple_blocks n)"
  then have "\<And> bl. bl \<in># \<B> \<Longrightarrow> count (multiple_blocks n) bl = 1"
    by (metis assms(1) elem_in_original_in_repeat not_gr_zero not_less_zero simple_design.simple)
  thus False using assms(1) assms(2) by auto 
qed

end
subsection \<open>Proper Designs\<close>
text \<open>Many types of designs rely on paramter conditions that only make sense for non-empty designs. 
i.e. designs with at least one block, and therefore given wellformed condition, at least one point. 
To this end we define the notion of a "proper" design \<close>

locale proper_design = design + 
  assumes b_non_zero: "\<b> \<noteq> 0"
begin

lemma is_proper: "proper_design \<V> \<B>" by intro_locales

lemma v_non_zero: "\<v> > 0"
  using b_non_zero v_eq0_imp_b_eq_0 by auto

lemma b_positive: "\<b> > 0" using b_non_zero
  by (simp add: nonempty_has_size)

lemma design_points_nempty: "\<V> \<noteq> {}"
  using v_non_zero by auto 

lemma design_blocks_nempty: "\<B> \<noteq> {#}"
  using b_non_zero by auto

end

lemma (in design) proper_designI[intro]: "\<b> \<noteq> 0 \<Longrightarrow> proper_design \<V> \<B>"
  by (unfold_locales) simp

lemma proper_designII[intro]: assumes "design V B" and "B \<noteq> {#}" shows "proper_design V B"
proof -
  interpret des: design V B using assms by simp
  show ?thesis using assms by unfold_locales simp
qed

context proper_design
begin

lemma combine_proper_design:
  assumes "design V' B'"
  shows "proper_design (\<V> \<union> V') (\<B> + B')"
  using assms by (simp add: combine_designs design_blocks_nempty proper_designII wf_design)

lemma multiple_proper_design: 
  assumes "n > 0"
  shows "proper_design \<V> (multiple_blocks n)"
  using multiple_is_design assms
  by (metis block_set_nempty_imp_block_ex design_blocks_nempty empty_iff multiple_block_in proper_designII set_mset_empty) 

lemma complement_proper_design: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  shows "proper_design \<V> (complement_blocks)"
proof -
  interpret des: design \<V> "(complement_blocks)"
    by (simp add: assms complement_design)  
  show ?thesis using b_non_zero by (unfold_locales) auto
qed

lemma delete_point_proper: 
  assumes "\<And>bl. bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> 2 \<le> card bl"
  shows "proper_design (points (delete_point p)) (blocks (delete_point p))"
proof -
  interpret des: design "points (delete_point p)" "blocks (delete_point p)"
    using delete_point_design assms by blast 
  show ?thesis using design_blocks_nempty by (unfold_locales) simp
qed

lemma strong_delete_point_proper: 
  assumes "\<And>bl. bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> 2 \<le> card bl"
  assumes "\<B> rep p < \<b>"
  shows "proper_design (points (strong_delete_point p)) (blocks (strong_delete_point p))"
proof -
  interpret des: design "points (strong_delete_point p)" "blocks (strong_delete_point p)"
    using strong_del_point_design assms by blast 
  show ?thesis using assms design_blocks_nempty point_rep_num_inv_non_empty 
    by (unfold_locales) simp
qed

end
end