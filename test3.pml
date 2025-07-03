/* Generated Promela code */
/* Translated from C using C-to-Promela translator */
/* Warning: Some C semantics may not be preserved */


/* Globals to simulate return values */
int main_result;

proctype main()
{
  int arr[3];
  arr[0] = 1;
  arr[1] = 2;
  arr[2] = arr[0] + arr[1];
  main_result = 0;
  // return 0 (Promela doesn't support return values)
}
