#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

struct Opt {
	int n= 9;
	char mode= 'c';
	string c_style= "errata"; // errata|old
	long long max_abs= 0;			// 0 disables cap
	int threads= 0;
};

static void usage(const char *p) {
	cerr << "Usage: " << p << " [--n 9] [--mode a|b|c] [--c-style errata|old]"
			 << " [--max-abs 0] [--threads N]\n";
	exit(1);
}

static Opt parse_args(int argc, char **argv) {
	Opt o;
	for(int i= 1; i < argc; i++) {
		string a= argv[i];
		if(a == "--n") {
			if(i + 1 >= argc) usage(argv[0]);
			o.n= stoi(argv[++i]);
		} else if(a == "--mode") {
			if(i + 1 >= argc) usage(argv[0]);
			o.mode= argv[++i][0];
		} else if(a == "--c-style") {
			if(i + 1 >= argc) usage(argv[0]);
			o.c_style= argv[++i];
		} else if(a == "--max-abs") {
			if(i + 1 >= argc) usage(argv[0]);
			o.max_abs= stoll(argv[++i]);
		} else if(a == "--threads") {
			if(i + 1 >= argc) usage(argv[0]);
			o.threads= stoi(argv[++i]);
		} else {
			usage(argv[0]);
		}
	}
	if(o.n < 1 || o.n > 9) {
		cerr << "n must be 1..9\n";
		exit(1);
	}
	if(o.mode != 'a' && o.mode != 'b' && o.mode != 'c') {
		cerr << "mode must be a|b|c\n";
		exit(1);
	}
	if(o.c_style != "errata" && o.c_style != "old") {
		cerr << "c-style must be errata|old\n";
		exit(1);
	}
	if(o.threads < 0) {
		cerr << "threads must be >= 0\n";
		exit(1);
	}
	return o;
}

static inline __int128 iabs128(__int128 x) { return x < 0 ? -x : x; }
static inline uint64_t uabs64(long long x) {
	return x < 0 ? (uint64_t)(-(x + 1)) + 1ULL : (uint64_t)x;
}
static inline uint64_t gcd64(uint64_t a, uint64_t b) {
	while(b) {
		uint64_t t= a % b;
		a= b;
		b= t;
	}
	return a == 0 ? 1 : a;
}
static inline __int128 gcd128(__int128 a, __int128 b) {
	a= iabs128(a);
	b= iabs128(b);
	while(b) {
		__int128 t= a % b;
		a= b;
		b= t;
	}
	return a == 0 ? 1 : a;
}
static inline bool fits_i64(__int128 x) {
	return x >= (__int128)LLONG_MIN && x <= (__int128)LLONG_MAX;
}

struct Frac {
	long long n= 0, d= 1;

	bool set(__int128 nn, __int128 dd) {
		if(dd == 0) return false;
		if(dd < 0) {
			dd= -dd;
			nn= -nn;
		}
		if(nn == 0) {
			n= 0;
			d= 1;
			return true;
		}
		if(fits_i64(nn) && fits_i64(dd)) {
			long long n64= (long long)nn;
			long long d64= (long long)dd;
			uint64_t g= gcd64(uabs64(n64), uabs64(d64));
			n64/= (long long)g;
			d64/= (long long)g;
			if(d64 < 0) {
				d64= -d64;
				n64= -n64;
			}
			n= n64;
			d= d64;
			return true;
		}
		__int128 g= gcd128(nn, dd);
		nn/= g;
		dd/= g;
		if(dd < 0) {
			dd= -dd;
			nn= -nn;
		}
		if(!fits_i64(nn) || !fits_i64(dd)) return false;
		n= (long long)nn;
		d= (long long)dd;
		return true;
	}
};

static inline bool in_cap(const Frac &v, long long cap) {
	return cap <= 0 || (llabs(v.n) <= cap && v.d <= cap);
}
static inline bool addf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.d + (__int128)b.n * a.d,
								 (__int128)a.d * b.d);
}
static inline bool subf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.d - (__int128)b.n * a.d,
								 (__int128)a.d * b.d);
}
static inline bool mulf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.n, (__int128)a.d * b.d);
}
static inline bool divf(const Frac &a, const Frac &b, Frac &out) {
	if(b.n == 0) return false;
	return out.set((__int128)a.n * b.d, (__int128)a.d * b.n);
}

struct Stats {
	unsigned long long syntax_attempts= 0;
	unsigned long long valid_exprs= 0;
	unsigned long long invalid_div_zero= 0;
	unsigned long long invalid_set_fail= 0;
	unsigned long long invalid_cap= 0;

	void add(const Stats &o) {
		syntax_attempts+= o.syntax_attempts;
		valid_exprs+= o.valid_exprs;
		invalid_div_zero+= o.invalid_div_zero;
		invalid_set_fail+= o.invalid_set_fail;
		invalid_cap+= o.invalid_cap;
	}
};

struct Collector {
	unordered_set<long long> ints;
	Stats stats;

	void note_root(bool valid, const Frac &v) {
		stats.syntax_attempts++;
		if(!valid) return;
		stats.valid_exprs++;
		if(v.d == 1) ints.insert(v.n);
	}
};

enum JobKind { JOB_ATOM= 0, JOB_BIN= 1 };

struct Job {
	JobKind kind;
	int k= 0;
	char op= 0;
};

class Enumerator {
public:
	using Emit= function<void(bool, const Frac &)>;

	explicit Enumerator(const Opt &opt_): opt(opt_) {}

	void emit_expr(int i, int j, Collector &col, const Emit &emit) const {
		emit_atom(i, j, col, emit);
		for(int k= i + 1; k < j; k++) {
			for(char op: string("+-*/")) {
				emit_expr(i, k, col, [&](bool lv, const Frac &a) {
					emit_expr(k, j, col, [&](bool rv, const Frac &b) {
						emit_binary(lv, a, rv, b, op, col, emit);
					});
				});
			}
		}
	}

	void emit_atom(int i, int j, Collector &col, const Emit &emit) const {
		int L= j - i;
		if(opt.mode == 'a') {
			if(L != 1) return;
			Frac f;
			if(!f.set(i + 1, 1)) {
				col.stats.invalid_set_fail++;
				emit(false, Frac{});
				return;
			}
			if(!in_cap(f, opt.max_abs)) {
				col.stats.invalid_cap++;
				emit(false, Frac{});
				return;
			}
			emit(true, f);
			return;
		}

		long long v= token_value(i, j);
		Frac f;
		if(f.set(v, 1)) {
			if(in_cap(f, opt.max_abs)) emit(true, f);
			else {
				col.stats.invalid_cap++;
				emit(false, Frac{});
			}
		} else {
			col.stats.invalid_set_fail++;
			emit(false, Frac{});
		}

		if(opt.mode != 'c') return;
		if(opt.c_style == "old") {
			emit_decimal(v, L, L, col, emit);
			return;
		}
		for(int t= 1; t <= L; t++) emit_decimal(v, t, L, col, emit);
	}

private:
	const Opt &opt;

	static long long pow10ll(int t) {
		long long p= 1;
		while(t--) p*= 10;
		return p;
	}

	long long token_value(int i, int j) const {
		long long v= 0;
		for(int k= i + 1; k <= j; k++) v= v * 10 + k;
		return v;
	}

	void emit_decimal(long long v, int t, int, Collector &col,
										const Emit &emit) const {
		Frac g;
		if(g.set(v, pow10ll(t))) {
			if(in_cap(g, opt.max_abs)) emit(true, g);
			else {
				col.stats.invalid_cap++;
				emit(false, Frac{});
			}
		} else {
			col.stats.invalid_set_fail++;
			emit(false, Frac{});
		}
	}

	void emit_binary(bool lv, const Frac &a, bool rv, const Frac &b, char op,
									 Collector &col, const Emit &emit) const {
		if(!lv || !rv) {
			emit(false, Frac{});
			return;
		}
		Frac v;
		bool ok= false;
		if(op == '+') ok= addf(a, b, v);
		else if(op == '-')
			ok= subf(a, b, v);
		else if(op == '*')
			ok= mulf(a, b, v);
		else if(op == '/')
			ok= divf(a, b, v);
		if(!ok) {
			if(op == '/' && b.n == 0) col.stats.invalid_div_zero++;
			else
				col.stats.invalid_set_fail++;
			emit(false, Frac{});
			return;
		}
		if(!in_cap(v, opt.max_abs)) {
			col.stats.invalid_cap++;
			emit(false, Frac{});
			return;
		}
		emit(true, v);
	}
};

static unsigned long long atom_count(int n, char mode, const string &c_style) {
	if(mode == 'a') return n == 1 ? 1ULL : 0ULL;
	if(mode == 'b') return 1ULL;
	if(c_style == "old") return 2ULL;
	return (unsigned long long)(n + 1);
}

static vector<unsigned long long> unrestricted_counts(int nmax, char mode,
																											const string &c_style) {
	vector<unsigned long long> f(nmax + 1, 0);
	for(int n= 1; n <= nmax; n++) {
		f[n]= atom_count(n, mode, c_style);
		for(int i= 1; i < n; i++) f[n]+= 4ULL * f[i] * f[n - i];
	}
	return f;
}

int main(int argc, char **argv) {
	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	Opt opt= parse_args(argc, argv);
	if(opt.threads > 0) omp_set_num_threads(opt.threads);

	Enumerator en(opt);
	vector<Job> jobs;
	jobs.push_back({JOB_ATOM, 0, 0});
	for(int k= 1; k < opt.n; k++) {
		for(char op: string("+-*/")) jobs.push_back({JOB_BIN, k, op});
	}

	vector<Collector> partial(jobs.size());

#pragma omp parallel for schedule(dynamic, 1)
	for(size_t idx= 0; idx < jobs.size(); idx++) {
		Collector &col= partial[idx];
		const Job job= jobs[idx];
		Enumerator::Emit root_emit= [&](bool valid, const Frac &v) {
			col.note_root(valid, v);
		};

		if(job.kind == JOB_ATOM) {
			en.emit_atom(0, opt.n, col, root_emit);
			continue;
		}

		en.emit_expr(0, job.k, col, [&](bool lv, const Frac &a) {
			en.emit_expr(job.k, opt.n, col, [&](bool rv, const Frac &b) {
				if(!lv || !rv) {
					root_emit(false, Frac{});
					return;
				}
				Frac v;
				bool ok= false;
				if(job.op == '+') ok= addf(a, b, v);
				else if(job.op == '-')
					ok= subf(a, b, v);
				else if(job.op == '*')
					ok= mulf(a, b, v);
				else if(job.op == '/')
					ok= divf(a, b, v);
				if(!ok) {
					if(job.op == '/' && b.n == 0) col.stats.invalid_div_zero++;
					else
						col.stats.invalid_set_fail++;
					root_emit(false, Frac{});
					return;
				}
				if(!in_cap(v, opt.max_abs)) {
					col.stats.invalid_cap++;
					root_emit(false, Frac{});
					return;
				}
				root_emit(true, v);
			});
		});
	}

	unordered_set<long long> ints;
	Stats stats;
	for(const auto &col: partial) {
		stats.add(col.stats);
		for(long long v: col.ints) ints.insert(v);
	}

	long long smallest_missing= 1;
	while(ints.find(smallest_missing) != ints.end()) smallest_missing++;

	auto counts= unrestricted_counts(opt.n, opt.mode, opt.c_style);

	cout << "model=openmp_catalan_representable\n";
	cout << "n=" << opt.n << " mode=" << opt.mode << " c_style=" << opt.c_style
			 << " max_abs=" << opt.max_abs << " threads=" << omp_get_max_threads()
			 << "\n";
	cout << "expected_syntax_attempts=" << counts[opt.n] << "\n";
	cout << "syntax_attempts=" << stats.syntax_attempts << "\n";
	cout << "valid_exprs=" << stats.valid_exprs << "\n";
	cout << "representable_integers=" << ints.size() << "\n";
	cout << "smallest_unreachable_positive=" << smallest_missing << "\n";
	cout << "invalid_div_zero=" << stats.invalid_div_zero << "\n";
	cout << "invalid_set_fail=" << stats.invalid_set_fail << "\n";
	cout << "invalid_cap=" << stats.invalid_cap << "\n";
	return 0;
}
