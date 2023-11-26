theory T_Pairing_Heap_List1
  imports "../src/TimingFunction" "afp/Pairing_Heap_List1"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun merge
define_time_fun insert
define_time_fun pass\<^sub>1
define_time_fun pass\<^sub>2
define_time_fun del_min

text \<open>Proove equality\<close>

end