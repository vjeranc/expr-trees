#include <bits/stdc++.h>
#include <boost/multiprecision/cpp_int.hpp>
using namespace std;
using boost::multiprecision::cpp_int;

struct Options {
  string ops = "+-*/^";
  int max_digits = 9;
  bool concat = false;
  bool dot = false;
  bool decimal_dot = false;
  string grammar = "precedence"; // precedence | dudeney
};

static void usage(const char* prog){
  cerr
    << "Usage:\n"
    << "  " << prog << " [--operators \"+-*/^\"] [--max-digits 9]"
    << " [--concat] [--dot | --decimal-dot] [--grammar precedence|dudeney]\n";
  exit(1);
}

static Options parse_args(int argc, char** argv){
  Options o;
  for(int i=1;i<argc;i++){
    string a = argv[i];
    if(a=="--operators"){ if(i+1>=argc) usage(argv[0]); o.ops = argv[++i]; }
    else if(a=="--max-digits"){ if(i+1>=argc) usage(argv[0]); o.max_digits = stoi(argv[++i]); }
    else if(a=="--max-leaves"){ if(i+1>=argc) usage(argv[0]); o.max_digits = stoi(argv[++i]); }
    else if(a=="--concat"){ o.concat = true; }
    else if(a=="--dot"){ o.dot = true; }
    else if(a=="--decimal-dot"){ o.decimal_dot = true; }
    else if(a=="--grammar"){ if(i+1>=argc) usage(argv[0]); o.grammar = argv[++i]; }
    else if(a=="-h" || a=="--help"){ usage(argv[0]); }
    else { cerr << "Unknown arg: " << a << "\n"; usage(argv[0]); }
  }
  if(o.dot && o.decimal_dot){
    cerr << "Error: --dot and --decimal-dot are mutually exclusive.\n";
    exit(1);
  }
  if(o.max_digits < 1 || o.max_digits > 200){
    cerr << "Error: --max-digits must be in [1,200].\n";
    exit(1);
  }
  if(o.grammar != "precedence" && o.grammar != "dudeney"){
    cerr << "Error: --grammar must be 'precedence' or 'dudeney'.\n";
    exit(1);
  }
  return o;
}

static array<bool,256> ops_mask(const string& ops){
  array<bool,256> m{}; m.fill(false);
  for(char c: ops){
    if(c=='+'||c=='-'||c=='*'||c=='/'||c=='^') m[(unsigned char)c]=true;
  }
  return m;
}

static string as_str(const cpp_int& x){
  ostringstream oss;
  oss << x;
  return oss.str();
}

int main(int argc, char** argv){
  ios::sync_with_stdio(false);
  cin.tie(nullptr);

  Options opt = parse_args(argc, argv);
  auto op = ops_mask(opt.ops);
  int N = opt.max_digits;

  // Atom count A(n): number of atomic literals over a span of n digits.
  // Mirrors digit_dp.cpp::gen_atoms semantics:
  // - concat off: only n=1 digit atom; optional --dot adds ".d" (still n=1 only).
  // - concat on: integer literal over whole span; optional --dot adds ".XYZ";
  //   optional --decimal-dot follows amended (c):
  //     <digit string> | .<digit string> | <digit string>.<digit string>
  //   so per span length n we add n dotted forms (1 leading + n-1 internal).
  vector<cpp_int> A(N+1);
  for(int n=1; n<=N; n++){
    cpp_int a = 0;
    if(!opt.concat){
      if(n==1){
        a += 1;           // d
        if(opt.dot) a += 1; // .d
      }
    } else {
      a += 1; // XYZ
      if(opt.dot) a += 1;          // .XYZ
      if(opt.decimal_dot) a += n; // .XYZ plus X.YZ, XY.Z, ...
    }
    A[n] = a;
  }

  vector<cpp_int> S(N+1), P(N+1), E(N+1);
  vector<cpp_int> NUM(N+1), FAC(N+1), POWX(N+1), POWCTX(N+1), TERM(N+1), PROD(N+1), QUOT(N+1), SUM(N+1), EXPR(N+1);

  if(opt.grammar == "precedence"){
    // Precedence/associativity counting on digit-span length n, with
    // parenthesized sums admitted as factors (e.g. (x+y)*z).
    //
    // We separate exact-root counts (yS,yP,yE) from expected-context
    // counts (Xs,Xp,Xe):
    //   Xs = yS + yP + yE
    //   Xp = yP + yE + yS_wrapped
    //   Xe = yE + yS_wrapped
    // where yS_wrapped has the same count as yS.
    //
    // Exact recurrences:
    //   yE = A + (^ ? sum Xs(l)*Xe(r) : 0)
    //   yP = (* ? sum Xp(l)*Xe(r) : 0) + (/ ? sum Xp(l)*Xp(r) : 0)
    //   yS = (+ ? sum Xs(l)*Xp(r) : 0) + (- ? sum Xs(l)*Xs(r) : 0)
    vector<cpp_int> yS(N+1), yP(N+1), yE(N+1), Xs(N+1), Xp(N+1), Xe(N+1);
    for(int n=1; n<=N; n++){
      yE[n] = A[n];
      if(op[(unsigned char)'^']){
        for(int l=1; l<n; l++){
          int r = n-l;
          yE[n] += Xs[l] * Xe[r];
        }
      }

      yP[n] = 0;
      for(int l=1; l<n; l++){
        int r = n-l;
        if(op[(unsigned char)'*']) yP[n] += Xp[l] * Xe[r];
        if(op[(unsigned char)'/']) yP[n] += Xp[l] * Xp[r];
      }

      yS[n] = 0;
      for(int l=1; l<n; l++){
        int r = n-l;
        if(op[(unsigned char)'+']) yS[n] += Xs[l] * Xp[r];
        if(op[(unsigned char)'-']) yS[n] += Xs[l] * Xs[r];
      }

      Xs[n] = yS[n] + yP[n] + yE[n];
      Xp[n] = yP[n] + yE[n] + yS[n];
      Xe[n] = yE[n] + yS[n];

      S[n] = Xs[n];
      P[n] = Xp[n];
      E[n] = Xe[n];
    }
  } else {
    // Dudeney-style canonicalization grammar with optional '^' extension:
    // expr -> number | sum | product | quotient
    // sum  -> term +/- term | sum +/- term
    // term -> number | power_exact | product | quotient
    // power -> factor | factor ^ power      (right-associative)
    // power_exact counts only roots with '^'; power_ctx = factor + power_exact
    // product  -> power*power | product*power | quotient*power
    // quotient -> power/power | product/power | quotient/power
    // factor -> number | (sum)
    int sum_ops = (op[(unsigned char)'+'] ? 1 : 0) + (op[(unsigned char)'-'] ? 1 : 0);
    int has_mul = op[(unsigned char)'*'] ? 1 : 0;
    int has_div = op[(unsigned char)'/'] ? 1 : 0;
    int has_pow = op[(unsigned char)'^'] ? 1 : 0;

    for(int n=1; n<=N; n++){
      NUM[n] = A[n];
      POWX[n] = 0;
      POWCTX[n] = 0;
      PROD[n] = 0;
      QUOT[n] = 0;
      SUM[n] = 0;

      for(int l=1; l<n; l++){
        int r = n-l;

        if(sum_ops){
          SUM[n] += (cpp_int)sum_ops * TERM[l] * TERM[r];
          SUM[n] += (cpp_int)sum_ops * SUM[l] * TERM[r];
        }
      }

      FAC[n] = NUM[n] + SUM[n];

      if(has_pow){
        POWCTX[n] = FAC[n];
        for(int l=1; l<n; l++){
          int r = n-l;
          POWX[n] += FAC[l] * POWCTX[r];
        }
        POWCTX[n] += POWX[n];
      }

      for(int l=1; l<n; l++){
        int r = n-l;
        cpp_int left_base = has_pow ? POWCTX[l] : FAC[l];
        cpp_int right_base = has_pow ? POWCTX[r] : FAC[r];
        if(has_mul){
          PROD[n] += left_base * right_base;
          PROD[n] += PROD[l] * right_base;
          PROD[n] += QUOT[l] * right_base;
        }

        if(has_div){
          QUOT[n] += left_base * right_base;
          QUOT[n] += PROD[l] * right_base;
          QUOT[n] += QUOT[l] * right_base;
        }
      }

      TERM[n] = NUM[n] + PROD[n] + QUOT[n];
      if(has_pow) TERM[n] += POWX[n];
      EXPR[n] = NUM[n] + SUM[n] + PROD[n] + QUOT[n];
      if(has_pow) EXPR[n] += POWX[n];
      if(opt.decimal_dot) EXPR[n] -= NUM[n]; // Knuth errata convention for (c) totals

      // align reporting slots with precedence output fields:
      P[n] = PROD[n] + QUOT[n];
      E[n] = has_pow ? POWX[n] : NUM[n];
      S[n] = EXPR[n];
    }
  }

  cout << "operators=\"" << opt.ops << "\" max_digits=" << N
       << " concat=" << (opt.concat?"on":"off")
       << " dot=" << (opt.dot?"on":"off")
       << " decimal-dot=" << (opt.decimal_dot?"on":"off")
       << " grammar=" << opt.grammar
       << "\n";
  if(opt.grammar == "precedence"){
    cout << "model=precedence_associativity_canonical_counts_with_atoms\n";
  } else {
    cout << "model=dudeney_canonical_counts_with_atoms\n";
  }
  for(int n=1; n<=N; n++){
    cout << "n=" << n
         << " atoms=" << as_str(A[n])
         << " expr=" << as_str(S[n])
         << " sum=" << as_str(S[n])
         << " prod=" << as_str(P[n])
         << " pow=" << as_str(E[n])
         << "\n";
  }
  return 0;
}
