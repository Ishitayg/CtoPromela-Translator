/* Generated Promela code */
/* Translated from C using C-to-Promela translator */
/* Warning: Some C semantics may not be preserved */


/* Globals to simulate return values */
int main_result;

proctype main()
{
  int x = 5;
  int y = 10;
  if
  :: (x < y) -> 
    {
      // Note: printf in Promela only executes during simulation, not verification
      printf(x is less than y\n);
    }
  :: else -> 
    {
      // Note: printf in Promela only executes during simulation, not verification
      printf(x is not less than y\n);
    }
  fi;
  main_result = 0;
  // return 0 (Promela doesn't support return values)
}
