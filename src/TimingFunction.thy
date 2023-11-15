theory TimingFunction
  imports Main
  keywords "define_time_fun" :: thy_decl
    and    "define_atime_fun" :: thy_decl
    and    "define_time_unit" :: thy_decl
begin

ML_file UnitFuns.ML
ML_file TimingFunction.ML

define_time_unit "(+)"
define_time_unit "(<)"
define_time_unit "Not"
define_time_unit "Num.numeral_class.numeral"

end