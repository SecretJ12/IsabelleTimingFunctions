theory Define_Time_Fun
  imports Main
  keywords "define_time_fun" :: thy_decl
    and    "equations"
    and    "define_time_0" :: thy_decl
begin

ML_file Define_Time_0.ML
ML_file Define_Time_Fun.ML

declare [[time_prefix = "T_"]]

define_time_0 "(+)"
define_time_0 "(-)"
define_time_0 "(*)"
define_time_0 "(/)"
define_time_0 "(div)"
define_time_0 "(<)"
define_time_0 "(\<le>)"
define_time_0 "Not"
define_time_0 "(\<and>)"
define_time_0 "(\<or>)"
define_time_0 "Num.numeral_class.numeral"
define_time_0 "(=)"

end