# timings_lib.g
# Shared runtime-reporting helper for GAP verification scripts.
# Enable timings via any of:
#   bash scripts/reproduce_all_outputs.sh --timings
#   SHOW_TIMINGS=1 gap -q scripts/<script>.g
#   gap -q -c 'SHOW_TIMINGS := true;' scripts/<script>.g
#   gap -q scripts/<script>.g --timings

if not IsBound(SHOW_TIMINGS) then
  SHOW_TIMINGS := ("--timings" in GAPInfo.SystemCommandLine) or
    (IsBound(GAPInfo.SystemEnvironment.SHOW_TIMINGS) and
     GAPInfo.SystemEnvironment.SHOW_TIMINGS in ["1", "true", "TRUE"]);
fi;
t_script_start := Runtime();
