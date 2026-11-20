# run_slice.g
# Parameterized exhaustive fixed-point search worker over consistent order-5^7 tuples
# with index i === SLICE_REM (mod 6).
# Usage:
#   SLICE_REM=0 gap -q --quitonbreak scripts/exhaustive_5_7/run_slice.g

Read("lib/param_5_7_lib.g");

if not IsBound(SLICE_REM) and IsBound(GAPInfo.SystemEnvironment.SLICE_REM) then
  SLICE_REM := Int(GAPInfo.SystemEnvironment.SLICE_REM);
fi;
if not IsBound(SLICE_REM) or not (SLICE_REM in [0..5]) then
  Error("SLICE_REM must be an integer in [0..5]");
fi;

if not IsBound(SLICE_OUT) then
  if IsBound(GAPInfo.SystemEnvironment.SLICE_OUT) then
    SLICE_OUT := GAPInfo.SystemEnvironment.SLICE_OUT;
  else
    SLICE_OUT := Concatenation("scripts/exhaustive_5_7/out", String(SLICE_REM), ".txt");
  fi;
fi;

RunExhaustive57Job(SLICE_REM, SLICE_OUT);
QUIT;
