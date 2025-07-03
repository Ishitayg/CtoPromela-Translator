/* Generated Promela code */
/* Translated from C using C-to-Promela translator */
/* Warning: Some C semantics may not be preserved */


/* Globals to simulate return values */
int main_result;

active proctype main()
{
  int i = 0;
  int sum = 0;
  int choice = 2;
  int result = 0;
  i = 0;
  do
  :: (i < 3) -> 
    {
      {
        sum = sum + i;
      }
      i = i + 1;
    }
  :: else -> break
  od;
  // Note: printf in Promela only executes during simulation, not verification
  printf("Sum after for loop: %d\n", sum);
  main_result = 0;
  // return 0 (Promela doesn't support return values)
}
