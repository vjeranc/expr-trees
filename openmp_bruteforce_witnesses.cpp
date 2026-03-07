#include <bits/stdc++.h>
#include <boost/unordered/unordered_flat_map.hpp>
#include <omp.h>
using namespace std;

struct Opt {
	int n= 9;
	char mode= 'c';
	string c_style= "errata"; // errata|old
	long long max_abs= 1000000000LL;
	int threads= 0;
	string output= "representable_integers_witnesses.tsv";
};

static void usage(const char *p) {
	cerr << "Usage: " << p << " [--n 9] [--mode a|b|c] [--c-style errata|old]"
			 << " [--max-abs 1000000000] [--threads N]"
			 << " [--output PATH]\n";
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
		} else if(a == "--output") {
			if(i + 1 >= argc) usage(argv[0]);
			o.output= argv[++i];
		} else {
			usage(argv[0]);
		}
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
	return llabs(v.n) <= cap && v.d <= cap;
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

static int prec_of(char op) {
	if(op == '*' || op == '/') return 2;
	if(op == '+' || op == '-') return 1;
	return 3;
}

struct Expr {
	Frac v;
	string s;
	int prec= 3;
	char op= 0;
};

static bool need_parens_left(char parent, const Expr &child) {
	return child.prec < prec_of(parent);
}

static bool need_parens_right(char parent, const Expr &child) {
	int p= prec_of(parent);
	if(child.prec < p) return true;
	if(child.prec > p) return false;
	if(parent == '+') return child.op == '-';
	if(parent == '-') return child.op == '+' || child.op == '-';
	if(parent == '*') return child.op == '/';
	if(parent == '/') return child.op == '*' || child.op == '/';
	return false;
}

static Expr combine_expr(char op, const Expr &a, const Expr &b, const Frac &v) {
	string ls= need_parens_left(op, a) ? "(" + a.s + ")" : a.s;
	string rs= need_parens_right(op, b) ? "(" + b.s + ")" : b.s;
	return Expr{v, ls + string(1, op) + rs, prec_of(op), op};
}

struct Witness {
	string expr;
};

static bool better_expr(const string &a, const string &b) {
	if(b.empty()) return true;
	if(a.size() != b.size()) return a.size() < b.size();
	return a < b;
}

struct Stats {
	unsigned long long root_attempts= 0;
	unsigned long long root_valid_exprs= 0;
};

struct Collector {
	boost::unordered_flat_map<long long, Witness> best;
	Stats stats;

	void note_root_attempt() { stats.root_attempts++; }

	void note_root(const Expr &e) {
		stats.root_valid_exprs++;
		if(e.v.d != 1) return;
		auto it= best.find(e.v.n);
		if(it == best.end()) {
			best.emplace(e.v.n, Witness{e.s});
			return;
		}
		if(better_expr(e.s, it->second.expr)) it->second.expr= e.s;
	}
};

enum JobKind {
	JOB_NUM= 0,
	JOB_SUM_TERM_TERM= 1,
	JOB_SUM_SUM_TERM= 2,
	JOB_PROD_FAC_FAC= 3,
	JOB_PROD_PROD_FAC= 4,
	JOB_PROD_QUOT_FAC= 5,
	JOB_QUOT_FAC_FAC= 6,
	JOB_QUOT_PROD_FAC= 7,
	JOB_QUOT_QUOT_FAC= 8,
};

struct Job {
	JobKind kind;
	int k= 0;
};

class Enumerator {
public:
	using Emit= function<void(const Expr &)>;

	explicit Enumerator(const Opt &opt_): opt(opt_) {}

	void emit_number(int i, int j, const Emit &emit) const {
		int L= j - i;
		if(opt.mode == 'a') {
			if(L != 1) return;
			Frac f;
			if(!f.set(i + 1, 1) || !in_cap(f, opt.max_abs)) return;
			emit(Expr{f, to_string(i + 1), 3, 0});
			return;
		}

		long long v= token_value(i, j);
		Frac f;
		if(f.set(v, 1) && in_cap(f, opt.max_abs)) emit(Expr{f, to_string(v), 3, 0});

		if(opt.mode != 'c') return;
		if(opt.c_style == "old") {
			Frac g;
			if(g.set(v, pow10ll(L)) && in_cap(g, opt.max_abs))
				emit(Expr{g, "." + to_string(v), 3, 0});
			return;
		}

		for(int t= 1; t <= L; t++) {
			Frac g;
			if(!g.set(v, pow10ll(t)) || !in_cap(g, opt.max_abs)) continue;
			if(t == L) {
				emit(Expr{g, "." + to_string(v), 3, 0});
			} else {
				string s= to_string(v);
				const int dot_pos= (int)s.size() - t;
				s.insert((size_t)dot_pos, 1, '.');
				emit(Expr{g, std::move(s), 3, 0});
			}
		}
	}

	void emit_factor(int i, int j, const Emit &emit) const {
		emit_number(i, j, emit);
		emit_sum(i, j, emit);
	}

	void emit_term(int i, int j, const Emit &emit) const {
		emit_number(i, j, emit);
		emit_product(i, j, emit);
		emit_quotient(i, j, emit);
	}

	void emit_sum(int i, int j, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_term(i, k, [&](const Expr &a) {
				emit_term(k, j, [&](const Expr &b) {
					emit_binary(a, b, emit, '+');
					emit_binary(a, b, emit, '-');
				});
			});
			emit_sum(i, k, [&](const Expr &a) {
				emit_term(k, j, [&](const Expr &b) {
					emit_binary(a, b, emit, '+');
					emit_binary(a, b, emit, '-');
				});
			});
		}
	}

	void emit_product(int i, int j, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_factor(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '*'); });
			});
			emit_product(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '*'); });
			});
			emit_quotient(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '*'); });
			});
		}
	}

	void emit_quotient(int i, int j, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_factor(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '/'); });
			});
			emit_product(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '/'); });
			});
			emit_quotient(i, k, [&](const Expr &a) {
				emit_factor(k, j, [&](const Expr &b) { emit_binary(a, b, emit, '/'); });
			});
		}
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

	void emit_binary(const Expr &a, const Expr &b, const Emit &emit,
									 char op) const {
		Frac v;
		bool ok= false;
		if(op == '+') ok= addf(a.v, b.v, v);
		else if(op == '-')
			ok= subf(a.v, b.v, v);
		else if(op == '*')
			ok= mulf(a.v, b.v, v);
		else if(op == '/')
			ok= divf(a.v, b.v, v);
		if(!ok || !in_cap(v, opt.max_abs)) return;
		emit(combine_expr(op, a, b, v));
	}
};

int main(int argc, char **argv) {
	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	Opt opt= parse_args(argc, argv);
	if(opt.threads > 0) omp_set_num_threads(opt.threads);
	const auto start= chrono::steady_clock::now();

	Enumerator en(opt);
	vector<Job> jobs;
	jobs.push_back({JOB_NUM, 0});
	for(int k= 1; k < opt.n; k++) {
		jobs.push_back({JOB_SUM_TERM_TERM, k});
		jobs.push_back({JOB_SUM_SUM_TERM, k});
		jobs.push_back({JOB_PROD_FAC_FAC, k});
		jobs.push_back({JOB_PROD_PROD_FAC, k});
		jobs.push_back({JOB_PROD_QUOT_FAC, k});
		jobs.push_back({JOB_QUOT_FAC_FAC, k});
		jobs.push_back({JOB_QUOT_PROD_FAC, k});
		jobs.push_back({JOB_QUOT_QUOT_FAC, k});
	}

	vector<Collector> partial(jobs.size());

#pragma omp parallel for schedule(dynamic, 1)
	for(size_t idx= 0; idx < jobs.size(); idx++) {
		Collector &col= partial[idx];
		const Job job= jobs[idx];
		const int i= 0;
		const int j= opt.n;
		const int k= job.k;
		auto root_emit= [&](const Expr &e) { col.note_root(e); };

		switch(job.kind) {
		case JOB_NUM:
			en.emit_number(i, j, [&](const Expr &e) {
				col.note_root_attempt();
				root_emit(e);
			});
			break;
		case JOB_SUM_TERM_TERM:
			en.emit_term(i, k, [&](const Expr &a) {
				en.emit_term(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(addf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('+', a, b, v));
					col.note_root_attempt();
					if(subf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('-', a, b, v));
				});
			});
			break;
		case JOB_SUM_SUM_TERM:
			en.emit_sum(i, k, [&](const Expr &a) {
				en.emit_term(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(addf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('+', a, b, v));
					col.note_root_attempt();
					if(subf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('-', a, b, v));
				});
			});
			break;
		case JOB_PROD_FAC_FAC:
			en.emit_factor(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('*', a, b, v));
				});
			});
			break;
		case JOB_PROD_PROD_FAC:
			en.emit_product(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('*', a, b, v));
				});
			});
			break;
		case JOB_PROD_QUOT_FAC:
			en.emit_quotient(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('*', a, b, v));
				});
			});
			break;
		case JOB_QUOT_FAC_FAC:
			en.emit_factor(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('/', a, b, v));
				});
			});
			break;
		case JOB_QUOT_PROD_FAC:
			en.emit_product(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('/', a, b, v));
				});
			});
			break;
		case JOB_QUOT_QUOT_FAC:
			en.emit_quotient(i, k, [&](const Expr &a) {
				en.emit_factor(k, j, [&](const Expr &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a.v, b.v, v) && in_cap(v, opt.max_abs))
						root_emit(combine_expr('/', a, b, v));
				});
			});
			break;
		}
	}

	boost::unordered_flat_map<long long, Witness> merged;
	unsigned long long root_attempts= 0;
	unsigned long long root_valid_exprs= 0;
	for(auto &col: partial) {
		root_attempts+= col.stats.root_attempts;
		root_valid_exprs+= col.stats.root_valid_exprs;
		for(auto &kv: col.best) {
			auto it= merged.find(kv.first);
			if(it == merged.end()) {
				merged.emplace(kv.first, std::move(kv.second));
			} else if(better_expr(kv.second.expr, it->second.expr)) {
				it->second= std::move(kv.second);
			}
		}
	}

	vector<pair<long long, string>> rows;
	rows.reserve(merged.size());
	for(auto &kv: merged) rows.push_back({kv.first, kv.second.expr});
	sort(rows.begin(), rows.end(),
			 [](const auto &a, const auto &b) { return a.first < b.first; });

	ofstream out(opt.output);
	for(const auto &row: rows) out << row.first << '\t' << row.second << '\n';
	out.close();

	const auto end= chrono::steady_clock::now();
	const double elapsed_s=
			chrono::duration_cast<chrono::duration<double>>(end - start).count();

	cout << "model=openmp_bruteforce_witnesses\n";
	cout << "n=" << opt.n << " mode=" << opt.mode << " c_style=" << opt.c_style
			 << " max_abs=" << opt.max_abs << " threads=" << omp_get_max_threads()
			 << "\n";
	cout << "representable_integers=" << rows.size() << "\n";
	cout << "root_attempts=" << root_attempts << "\n";
	cout << "root_valid_exprs=" << root_valid_exprs << "\n";
	cout << "output=" << opt.output << "\n";
	cout << fixed << setprecision(3) << "elapsed_seconds=" << elapsed_s << "\n";
	return 0;
}
