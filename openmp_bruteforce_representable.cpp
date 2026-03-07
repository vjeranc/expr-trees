#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

struct Opt {
	int n= 9;
	char mode= 'c';
	string c_style= "errata"; // errata|old
	long long max_abs= 1000000000LL;
	int threads= 0;
};

static void usage(const char *p) {
	cerr << "Usage: " << p << " [--n 9] [--mode a|b|c] [--c-style errata|old]"
			 << " [--max-abs 1000000000] [--threads N]\n";
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

struct Stats {
	unsigned long long root_attempts= 0;
	unsigned long long root_valid_exprs= 0;
	unsigned long long atom_set_failures= 0;
	unsigned long long atom_cap_rejections= 0;
	unsigned long long combine_set_failures= 0;
	unsigned long long combine_cap_rejections= 0;

	void add(const Stats &o) {
		root_attempts+= o.root_attempts;
		root_valid_exprs+= o.root_valid_exprs;
		atom_set_failures+= o.atom_set_failures;
		atom_cap_rejections+= o.atom_cap_rejections;
		combine_set_failures+= o.combine_set_failures;
		combine_cap_rejections+= o.combine_cap_rejections;
	}
};

struct Collector {
	unordered_set<long long> ints;
	Stats stats;

	void note_root_attempt() { stats.root_attempts++; }

	void note_root(const Frac &v) {
		stats.root_valid_exprs++;
		if(v.d == 1) ints.insert(v.n);
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
	using Emit= function<void(const Frac &)>;

	explicit Enumerator(const Opt &opt_): opt(opt_) {}

	void emit_number(int i, int j, Collector &col, const Emit &emit) const {
		int L= j - i;
		if(opt.mode == 'a') {
			if(L != 1) return;
			Frac f;
			if(!f.set(i + 1, 1)) {
				col.stats.atom_set_failures++;
				return;
			}
			if(!in_cap(f, opt.max_abs)) {
				col.stats.atom_cap_rejections++;
				return;
			}
			emit(f);
			return;
		}

		long long v= token_value(i, j);
		Frac f;
		if(f.set(v, 1)) {
			if(in_cap(f, opt.max_abs)) emit(f);
			else
				col.stats.atom_cap_rejections++;
		} else {
			col.stats.atom_set_failures++;
		}

		if(opt.mode != 'c') return;
		if(opt.c_style == "old") {
			Frac g;
			if(g.set(v, pow10ll(L))) {
				if(in_cap(g, opt.max_abs)) emit(g);
				else
					col.stats.atom_cap_rejections++;
			} else {
				col.stats.atom_set_failures++;
			}
			return;
		}

		for(int t= 1; t <= L; t++) {
			Frac g;
			if(g.set(v, pow10ll(t))) {
				if(in_cap(g, opt.max_abs)) emit(g);
				else
					col.stats.atom_cap_rejections++;
			} else {
				col.stats.atom_set_failures++;
			}
		}
	}

	void emit_factor(int i, int j, Collector &col, const Emit &emit) const {
		emit_number(i, j, col, emit);
		emit_sum(i, j, col, emit);
	}

	void emit_term(int i, int j, Collector &col, const Emit &emit) const {
		emit_number(i, j, col, emit);
		emit_product(i, j, col, emit);
		emit_quotient(i, j, col, emit);
	}

	void emit_sum(int i, int j, Collector &col, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_term(i, k, col, [&](const Frac &a) {
				emit_term(k, j, col, [&](const Frac &b) {
					emit_binary(a, b, col, emit, '+');
					emit_binary(a, b, col, emit, '-');
				});
			});
			emit_sum(i, k, col, [&](const Frac &a) {
				emit_term(k, j, col, [&](const Frac &b) {
					emit_binary(a, b, col, emit, '+');
					emit_binary(a, b, col, emit, '-');
				});
			});
		}
	}

	void emit_product(int i, int j, Collector &col, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_factor(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '*'); });
			});
			emit_product(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '*'); });
			});
			emit_quotient(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '*'); });
			});
		}
	}

	void emit_quotient(int i, int j, Collector &col, const Emit &emit) const {
		for(int k= i + 1; k < j; k++) {
			emit_factor(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '/'); });
			});
			emit_product(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '/'); });
			});
			emit_quotient(i, k, col, [&](const Frac &a) {
				emit_factor(k, j, col,
										[&](const Frac &b) { emit_binary(a, b, col, emit, '/'); });
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

	void emit_binary(const Frac &a, const Frac &b, Collector &col,
									 const Emit &emit, char op) const {
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
			col.stats.combine_set_failures++;
			return;
		}
		if(!in_cap(v, opt.max_abs)) {
			col.stats.combine_cap_rejections++;
			return;
		}
		emit(v);
	}
};

int main(int argc, char **argv) {
	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	Opt opt= parse_args(argc, argv);
	if(opt.threads > 0) omp_set_num_threads(opt.threads);

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
		Enumerator::Emit root_emit= [&](const Frac &v) { col.note_root(v); };

		switch(job.kind) {
		case JOB_NUM:
			en.emit_number(i, j, col, [&](const Frac &v) {
				col.note_root_attempt();
				root_emit(v);
			});
			break;
		case JOB_SUM_TERM_TERM:
			en.emit_term(i, k, col, [&](const Frac &a) {
				en.emit_term(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(addf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
					col.note_root_attempt();
					if(subf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_SUM_SUM_TERM:
			en.emit_sum(i, k, col, [&](const Frac &a) {
				en.emit_term(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(addf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
					col.note_root_attempt();
					if(subf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_PROD_FAC_FAC:
			en.emit_factor(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_PROD_PROD_FAC:
			en.emit_product(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_PROD_QUOT_FAC:
			en.emit_quotient(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(mulf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_QUOT_FAC_FAC:
			en.emit_factor(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_QUOT_PROD_FAC:
			en.emit_product(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		case JOB_QUOT_QUOT_FAC:
			en.emit_quotient(i, k, col, [&](const Frac &a) {
				en.emit_factor(k, j, col, [&](const Frac &b) {
					col.note_root_attempt();
					Frac v;
					if(divf(a, b, v)) {
						if(in_cap(v, opt.max_abs)) root_emit(v);
						else
							col.stats.combine_cap_rejections++;
					} else {
						col.stats.combine_set_failures++;
					}
				});
			});
			break;
		}
	}

	unordered_set<long long> ints;
	Stats stats;
	for(const auto &col: partial) {
		stats.add(col.stats);
		for(long long v: col.ints) ints.insert(v);
	}

	long long smallest_missing= 1;
	while(ints.find(smallest_missing) != ints.end()) smallest_missing++;

	cout << "model=openmp_bruteforce_representable\n";
	cout << "n=" << opt.n << " mode=" << opt.mode << " c_style=" << opt.c_style
			 << " max_abs=" << opt.max_abs << " threads=" << omp_get_max_threads()
			 << "\n";
	cout << "representable_integers=" << ints.size() << "\n";
	cout << "smallest_unreachable_positive=" << smallest_missing << "\n";
	cout << "root_attempts=" << stats.root_attempts << "\n";
	cout << "root_valid_exprs=" << stats.root_valid_exprs << "\n";
	cout << "atom_set_failures=" << stats.atom_set_failures << "\n";
	cout << "atom_cap_rejections=" << stats.atom_cap_rejections << "\n";
	cout << "combine_set_failures=" << stats.combine_set_failures << "\n";
	cout << "combine_cap_rejections=" << stats.combine_cap_rejections << "\n";
	return 0;
}
