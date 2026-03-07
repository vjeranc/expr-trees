#include <bits/stdc++.h>
#include <boost/unordered/unordered_flat_set.hpp>
using namespace std;

struct Opt {
	int n= 9;
	string modes= "abc";
	long long max_abs= 1000000000LL;
	bool leading_minus= false;
	string c_style= "errata";	 // errata|old
	string side_prune= "none"; // none|feasible
};

static void usage(const char *p) {
	cerr << "Usage: " << p
			 << " [--n 9] [--modes abc] [--max-abs 1000000000] [--leading-minus] "
					"[--c-style errata|old] [--side-prune none|feasible]\n";
	exit(1);
}

static Opt parse_args(int argc, char **argv) {
	Opt o;
	for(int i= 1; i < argc; i++) {
		string a= argv[i];
		if(a == "--n") {
			if(i + 1 >= argc) usage(argv[0]);
			o.n= stoi(argv[++i]);
		} else if(a == "--modes") {
			if(i + 1 >= argc) usage(argv[0]);
			o.modes= argv[++i];
		} else if(a == "--max-abs") {
			if(i + 1 >= argc) usage(argv[0]);
			o.max_abs= stoll(argv[++i]);
		} else if(a == "--leading-minus") {
			o.leading_minus= true;
		} else if(a == "--c-style") {
			if(i + 1 >= argc) usage(argv[0]);
			o.c_style= argv[++i];
		} else if(a == "--side-prune") {
			if(i + 1 >= argc) usage(argv[0]);
			o.side_prune= argv[++i];
		} else
			usage(argv[0]);
	}
	if(o.n < 1 || o.n > 9) {
		cerr << "n must be 1..9\n";
		exit(1);
	}
	for(char c: o.modes) {
		if(c != 'a' && c != 'b' && c != 'c') {
			cerr << "modes must contain only a,b,c\n";
			exit(1);
		}
	}
	if(o.c_style != "errata" && o.c_style != "old") {
		cerr << "--c-style must be errata|old\n";
		exit(1);
	}
	if(o.side_prune != "none" && o.side_prune != "feasible") {
		cerr << "--side-prune must be none|feasible\n";
		exit(1);
	}
	sort(o.modes.begin(), o.modes.end());
	o.modes.erase(unique(o.modes.begin(), o.modes.end()), o.modes.end());
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
	bool operator==(const Frac &o) const { return n == o.n && d == o.d; }
	bool operator<(const Frac &o) const { return n != o.n ? n < o.n : d < o.d; }
};

struct FracHash {
	size_t operator()(const Frac &x) const noexcept {
		uint64_t a= (uint64_t)x.n, b= (uint64_t)x.d;
		uint64_t h= a ^ (b + 0x9e3779b97f4a7c15ULL + (a << 6) + (a >> 2));
		return (size_t)h;
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

enum NT { NUM= 0, FAC= 1, TERM= 2, SUM= 3, PROD= 4, QUOT= 5, EXPR= 6, NTN= 7 };

struct Ctx {
	int n;
	char mode;
	bool c_old;
	bool side_prune_feasible;
	long long max_abs;
	int sideA, sideB;
	unsigned long long atom_set_failures= 0;
	unsigned long long atom_cap_rejections= 0;
	unsigned long long combine_set_failures= 0;
	unsigned long long combine_cap_rejections= 0;
	vector<array<vector<Frac>, NTN>> values;
	vector<array<boost::unordered_flat_set<Frac, FracHash>, NTN>> value_sets;
	vector<array<char, NTN>> built;

	explicit Ctx(int n_, char mode_, bool c_old_, bool side_prune_, long long cap)
			: n(n_), mode(mode_), c_old(c_old_), side_prune_feasible(side_prune_),
				max_abs(cap), sideA(n >= 2 ? cid(0, n - 1, n) : -1),
				sideB(n >= 2 ? cid(1, n, n) : -1), values(n * (n + 1) / 2),
				value_sets(n * (n + 1) / 2),
				built(n * (n + 1) / 2, array<char, NTN>{}) {}

	static int cid(int i, int j, int n) {
		return i * (2 * n - i + 1) / 2 + (j - i - 1);
	}
	int id(int i, int j) const { return cid(i, j, n); }

	long long token_value(int i, int j) const {
		long long v= 0;
		for(int k= i + 1; k <= j; k++) v= v * 10 + k;
		return v;
	}
	static long long pow10ll(int t) {
		long long p= 1;
		while(t--) p*= 10;
		return p;
	}

	vector<Frac> gen_atoms(int i, int j) {
		vector<Frac> out;
		int L= j - i;
		if(mode == 'a') {
			if(L == 1) {
				Frac f;
				if(f.set(i + 1, 1)) {
					if(in_cap(f, max_abs)) out.push_back(f);
					else
						atom_cap_rejections++;
				} else {
					atom_set_failures++;
				}
			}
			return out;
		}
		long long v= token_value(i, j);
		Frac f;
		if(f.set(v, 1)) {
			if(in_cap(f, max_abs)) out.push_back(f);
			else
				atom_cap_rejections++;
		} else {
			atom_set_failures++;
		}
		if(mode == 'c') {
			if(c_old) {
				Frac g;
				if(g.set(v, pow10ll(L))) {
					if(in_cap(g, max_abs)) out.push_back(g);
					else
						atom_cap_rejections++;
				} else {
					atom_set_failures++;
				}
			} else {
				for(int t= 1; t <= L; t++) {
					Frac g;
					if(g.set(v, pow10ll(t))) {
						if(in_cap(g, max_abs)) out.push_back(g);
						else
							atom_cap_rejections++;
					} else {
						atom_set_failures++;
					}
				}
			}
		}
		sort(out.begin(), out.end());
		out.erase(unique(out.begin(), out.end(),
										 [](const Frac &a, const Frac &b) { return a == b; }),
							out.end());
		return out;
	}

	bool keep_side_value(int c, const Frac &v) const {
		if(!side_prune_feasible) return true;
		if(c != sideA && c != sideB) return true;
		if(c == sideA) return (n % v.d == 0);
		return (v.d == 1 || llabs(v.n) == 1);
	}

	void add_unique(int c, int nt, const Frac &v) {
		if(!keep_side_value(c, v)) return;
		auto &s= value_sets[c][nt];
		auto ins= s.insert(v);
		if(ins.second) values[c][nt].push_back(v);
	}

	const vector<Frac> &get_values(int i, int j, int nt) {
		int c= id(i, j);
		if(built[c][nt]) return values[c][nt];
		built[c][nt]= 1;
		auto &out_set= value_sets[c][nt];

		if(nt == NUM) {
			for(const auto &v: gen_atoms(i, j)) add_unique(c, nt, v);
			return values[c][nt];
		}
		if(nt == FAC) {
			const auto &s= get_values(i, j, SUM);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: s) add_unique(c, nt, v);
			return values[c][nt];
		}
		if(nt == TERM) {
			const auto &p= get_values(i, j, PROD);
			const auto &q= get_values(i, j, QUOT);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: p) add_unique(c, nt, v);
			for(const auto &v: q) add_unique(c, nt, v);
			return values[c][nt];
		}
		if(nt == EXPR) {
			const auto &s= get_values(i, j, SUM);
			const auto &p= get_values(i, j, PROD);
			const auto &q= get_values(i, j, QUOT);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: s) add_unique(c, nt, v);
			for(const auto &v: p) add_unique(c, nt, v);
			for(const auto &v: q) add_unique(c, nt, v);
			return values[c][nt];
		}

		Frac v;
		if(nt == SUM) {
			for(int k= i + 1; k < j; k++) {
				const auto &lt= get_values(i, k, TERM);
				const auto &ls= get_values(i, k, SUM);
				const auto &rt= get_values(k, j, TERM);
				for(const auto &a: lt)
					for(const auto &b: rt) {
						if(addf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
						if(subf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
					}
				for(const auto &a: ls)
					for(const auto &b: rt) {
						if(addf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
						if(subf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
					}
			}
			return values[c][nt];
		}
		if(nt == PROD) {
			for(int k= i + 1; k < j; k++) {
				const auto &lf= get_values(i, k, FAC);
				const auto &lp= get_values(i, k, PROD);
				const auto &lq= get_values(i, k, QUOT);
				const auto &rf= get_values(k, j, FAC);
				for(const auto &a: lf)
					for(const auto &b: rf) {
						if(mulf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
					}
				for(const auto &a: lp)
					for(const auto &b: rf) {
						if(mulf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
					}
				for(const auto &a: lq)
					for(const auto &b: rf) {
						if(mulf(a, b, v)) {
							if(in_cap(v, max_abs)) add_unique(c, nt, v);
							else
								combine_cap_rejections++;
						} else {
							combine_set_failures++;
						}
					}
			}
			return values[c][nt];
		}
		for(int k= i + 1; k < j; k++) {
			const auto &lf= get_values(i, k, FAC);
			const auto &lp= get_values(i, k, PROD);
			const auto &lq= get_values(i, k, QUOT);
			const auto &rf= get_values(k, j, FAC);
			for(const auto &a: lf)
				for(const auto &b: rf) {
					if(divf(a, b, v)) {
						if(in_cap(v, max_abs)) add_unique(c, nt, v);
						else
							combine_cap_rejections++;
					} else {
						combine_set_failures++;
					}
				}
			for(const auto &a: lp)
				for(const auto &b: rf) {
					if(divf(a, b, v)) {
						if(in_cap(v, max_abs)) add_unique(c, nt, v);
						else
							combine_cap_rejections++;
					} else {
						combine_set_failures++;
					}
				}
			for(const auto &a: lq)
				for(const auto &b: rf) {
					if(divf(a, b, v)) {
						if(in_cap(v, max_abs)) add_unique(c, nt, v);
						else
							combine_cap_rejections++;
					} else {
						combine_set_failures++;
					}
				}
		}
		return values[c][nt];
	}
};

static void report_mode(const Opt &opt, char mode) {
	Ctx ctx(opt.n, mode, opt.c_style == "old", opt.side_prune == "feasible",
					opt.max_abs);
	const auto &root= ctx.get_values(0, opt.n, EXPR);

	unordered_set<long long> ints;
	for(const auto &x: root) {
		if(x.d == 1) ints.insert(x.n);
	}

	if(opt.leading_minus) {
		vector<long long> cur;
		for(long long v: ints) cur.push_back(v);
		for(long long v: cur) ints.insert(-v);
	}

	long long smallest_missing= 1;
	while(ints.find(smallest_missing) != ints.end()) smallest_missing++;

	cout << "mode=" << mode << " n=" << opt.n << " c_style=" << opt.c_style
			 << " side_prune=" << opt.side_prune
			 << " leading_minus=" << (opt.leading_minus ? "on" : "off") << "\n";
	cout << "root_unique_values=" << root.size() << "\n";
	cout << "representable_integers=" << ints.size() << "\n";
	cout << "smallest_unreachable_positive=" << smallest_missing << "\n";
	cout << "atom_set_failures=" << ctx.atom_set_failures << "\n";
	cout << "atom_cap_rejections=" << ctx.atom_cap_rejections << "\n";
	cout << "combine_set_failures=" << ctx.combine_set_failures << "\n";
	cout << "combine_cap_rejections=" << ctx.combine_cap_rejections << "\n";
}

int main(int argc, char **argv) {
	Opt opt= parse_args(argc, argv);
	for(char m: opt.modes) {
		report_mode(opt, m);
		cout << "---\n";
	}
	return 0;
}
