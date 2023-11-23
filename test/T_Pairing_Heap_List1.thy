theory T_Pairing_Heap_List1
  imports "../src/TimingFunction" "afp/Pairing_Heap_List1"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>merge includes let via :=\<close>
text \<open>insert uses merge\<close>
text \<open>del_min uses merge\<close>
text \<open>pass_1 uses merge\<close>
text \<open>pass_2 uses merge\<close>

text \<open>Proove equality\<close>


end