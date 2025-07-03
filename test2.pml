/* Generated Promela code */
/* Translated from C using C-to-Promela translator */
/* Warning: Some C semantics may not be preserved */

int a;
// Note: float is approximated using int in Promela
int b;
// Note: double is approximated using int in Promela
int c;
byte d;
int e = 5;
// Note: float is approximated using int in Promela
int f = 3 /* approx. 3.14 */;
// Note: double is approximated using int in Promela
int g = 2 /* approx. 2.71828 */;
byte h = 88 /* 'X' */;

/* Globals to simulate return values */
int calculate_result;
int get_pi_result;
byte get_grade_result;
int main_result;

proctype calculate(int x, int y /* float */, int z /* double */, byte op)
{
  if
  :: (op == 43 /* '+' */) -> 
    {
      // Note: printf in Promela only executes during simulation, not verification
      printf("Adding %d and %d\n", x, y);
      calculate_result = x + y + z;
      // return x + y + z (Promela doesn't support return values)
    }
  :: else -> 
    if
    :: (op == 42 /* '*' */) -> 
      {
        // Note: printf in Promela only executes during simulation, not verification
        printf("Multiplying %d and %d\n", x, y);
        calculate_result = x * y * z;
        // return x * y * z (Promela doesn't support return values)
      }
    :: else -> 
      {
        // Note: printf in Promela only executes during simulation, not verification
        printf("Unknown operation: %c\n", op);
        calculate_result = 0;
        // return 0 (Promela doesn't support return values)
      }
    fi;
  fi;
}
proctype get_pi()
/* Note: Function with float return type - return values not supported in Promela */
{
  get_pi_result = 3 /* approx. 3.14159 */;
  // return 3 /* approx. 3.14159 */ (Promela doesn't support return values)
}
proctype get_grade(int score)
/* Note: Function with char return type - return values not supported in Promela */
{
  if
  :: (score >= 90) -> 
    {
      get_grade_result = 65 /* 'A' */;
      // return 65 /* 'A' */ (Promela doesn't support return values)
    }
  :: else -> 
    if
    :: (score >= 80) -> 
      {
        get_grade_result = 66 /* 'B' */;
        // return 66 /* 'B' */ (Promela doesn't support return values)
      }
    :: else -> 
      if
      :: (score >= 70) -> 
        {
          get_grade_result = 67 /* 'C' */;
          // return 67 /* 'C' */ (Promela doesn't support return values)
        }
      :: else -> 
        if
        :: (score >= 60) -> 
          {
            get_grade_result = 68 /* 'D' */;
            // return 68 /* 'D' */ (Promela doesn't support return values)
          }
        :: else -> 
          {
            get_grade_result = 70 /* 'F' */;
            // return 70 /* 'F' */ (Promela doesn't support return values)
          }
        fi;
      fi;
    fi;
  fi;
}
active proctype main()
{
  a = 10;
  b = 20 /* approx. 20.5 */;
  c = 30 /* approx. 30.75 */;
  d = 90 /* 'Z' */;
  if
  :: (d == 90 /* 'Z' */) -> 
    {
      // Note: printf in Promela only executes during simulation, not verification
      printf("d is Z\n");
    }
  :: else -> 
    {
      // Note: printf in Promela only executes during simulation, not verification
      printf("d is not Z\n");
    }
  fi;
  int result;
  run calculate(a, b, c, 43 /* '+' */);
  result = calculate_result;
  // Note: printf in Promela only executes during simulation, not verification
  printf("Result of calculation: %d\n", result);
  // Note: float is approximated using int in Promela
  int pi = run get_pi();
  // Note: printf in Promela only executes during simulation, not verification
  printf("Value of pi: %d\n", pi);
  byte grade = run get_grade(85);
  // Note: printf in Promela only executes during simulation, not verification
  printf("Grade: %c\n", grade);
  main_result = 0;
  // return 0 (Promela doesn't support return values)
}
