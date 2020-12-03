/*
Copyright 2020, Yves Gallot

wieferich is free source code, under the MIT license (see LICENSE). You can redistribute, use and/or modify it.
Please give feedback to the authors if improvement is realized. It is distributed in the hope that it will be useful.
*/

#include <cstdint>
#define _USE_MATH_DEFINES
#include <cmath>
#include <iostream>
#include <queue>
#include <thread>
#include <mutex>
#include <chrono>

inline int log2_64(const uint64_t x) { return 63 - __builtin_clzll(x); }

typedef uint64_t vec4_uint64_t[4] __attribute__((aligned(32)));

inline void vec4_set(vec4_uint64_t y, const vec4_uint64_t x) { for (size_t i = 0; i < 4; ++i) y[i] = x[i]; }

// 2^64 * u - p * p_inv = 1, binary extended GCD
inline uint64_t invert(const uint64_t p)
{
	const uint64_t a_2 = uint64_t(1) << 63, b = p;
	uint64_t g1 = a_2, g2 = b, t = a_2, s = (1 + b) / 2;
	while (g1 != 1)
	{
		if (g1 > g2)
		{
			g1 /= 2;
			t /= 2;
			if (s % 2 != 0)
			{
				s += b;
				t += a_2;
			}
			s /= 2;
		}
		else g2 -= g1;
	}
	return -t;
}

struct M2p { uint64_t l, h; };

inline M2p dup(const M2p & x, const uint64_t p)
{
	M2p r;
	const bool c = (x.l >= p - x.l);
	const uint64_t sl = x.l + x.l;
	r.l = c ? sl - p : sl;

	uint64_t xh = c ? x.h + 1 : x.h;		// 0 <= xh <= p
	const uint64_t sh = xh + x.h;			// 0 <= sh < 2p
	r.h = (xh >= p - x.h) ? sh - p : sh;	// 0 <= r.h < p
	return r;
}

// Dorais, F. G.; Klyve, D., "A Wieferich Prime Search Up to 6.7x10^15", Journal of Integer Sequences. 14 (9), 2011.
inline M2p square(const M2p & x, const uint64_t p, const uint64_t q)
{
	const __uint128_t t = x.l * __uint128_t(x.l);
	const uint64_t u0 = q * uint64_t(t);
	const uint64_t t1 = uint64_t(t >> 64);
	const uint64_t v1 = uint64_t((p * __uint128_t(u0)) >> 64);

	const __uint128_t xlh = x.l * __uint128_t(x.h);
	const __uint128_t xlhu = xlh + u0;
	const __uint128_t tp = xlhu + xlh; const uint32_t tpc = (tp < xlh) ? 1 : 0;
	const uint64_t up0 = q * uint64_t(tp);
	const __int128_t t1p = uint64_t(tp >> 64) | (__uint128_t(tpc) << 64);
	const uint64_t v1p = uint64_t((p * __uint128_t(up0)) >> 64);

	__int128_t z0 = __int128_t(t1) - __int128_t(v1);	// -p < z0 < p
	__int128_t z1 = t1p - __int128_t(v1p);				// -p < z1 < 2p
	if (z0 < 0) { z0 += p; z1--; }
	else if (z0 >= p) { z0 -= p; z1++; }
	if (z1 < 0) { z1 += p; }
	else if (z1 >= p)
	{
		z1 -= p;
		if (z1 >= p) z1 -= p;
	}
	M2p r; r.l = z0; r.h = z1;
	return r;
}

inline M2p mul_1(const M2p & x, const uint64_t p, const uint64_t q)
{
	const uint64_t u0 = q * x.l;
	const uint64_t v1 = uint64_t((p * __uint128_t(u0)) >> 64);

	const __uint128_t tp = x.h + __uint128_t(u0);
	const uint64_t up0 = q * uint64_t(tp);
	const uint64_t t1p = uint64_t(tp >> 64);
	const uint64_t v1p = uint64_t((p * __uint128_t(up0)) >> 64);

	__int128_t z0 = -__int128_t(v1), z1 = __int128_t(t1p) - __int128_t(v1p);
	if (z0 < 0) { z0 += p; z1--; }
	if (z1 < 0) { z1 += p; }
	else if (z1 >= p)
	{
		z1 -= p;
		if (z1 >= p) z1 -= p;
	}
	M2p r; r.l = z0; r.h = z1;
	return r;
}

inline M2p two_pow_mod2(const uint64_t n, const uint64_t p)
{
	const uint64_t q = invert(p);

	M2p one;	// 2^64 mod p^2, the Montgomery (2^64, p^2) residue of 1
	if (p < (uint64_t(1) << 32))
	{
		// r_p2 = 2^64 mod p^2
		const uint64_t p2 = p * p;
		const int s = 63 - log2_64(p2);
		uint64_t m = p2 << s, r_p2 = -m;
		for (int i = 0; i < s; ++i) { m >>= 1; if (r_p2 >= m) r_p2 -= m; }
		one.l = r_p2 % p; one.h = r_p2 / p;
	}
	else
	{
		// 2^64 mod p^2 = 2^64 then compute 2^64 mod p
		const uint64_t mp = -p;
		one.l = mp % p; one.h = mp / p + 1;
	}

	M2p x; x = dup(one, p);
	for (uint64_t b = (uint64_t(1) << (log2_64(n) - 1)); b != 0; b >>= 1)
	{
		x = square(x, p, q);
		if ((n & b) != 0) x = dup(x, p);
	}
	return mul_1(x, p, q);
}

class Wieferich
{
private:
	static const size_t p_size = 256;

	struct PArray
	{
		vec4_uint64_t data[p_size];	// 8 KB

		void get(const size_t i, vec4_uint64_t p) { vec4_set(p, data[i]); }
	};

	class PArrayFiller
	{
	private:
		PArray & _p_array;
		size_t _iv = 0, _ia = 0;
		vec4_uint64_t _v;

	public:
		PArrayFiller(PArray & p_array) : _p_array(p_array) {}
		virtual ~PArrayFiller() {};

		bool add(const uint64_t p)
		{
			_v[_iv] = p;
			_iv = (_iv + 1) % 4;
			if (_iv == 0)
			{
				vec4_set(_p_array.data[_ia], _v);
				_ia = (_ia + 1) % p_size;
				return (_ia == 0);
			}
			return false;
		}
	};

private:
	const uint32_t _p_min, _p_max;

	static const size_t max_queue_size = 1024;

	std::mutex _p_queue_mutex;
	std::queue<PArray> _p_queue;

private:
	void prime_gen()
	{
		static const uint32_t sp_max = 1 << 16;
		static const size_t sieve_size = sp_max / 2;	// sieve with an odd prime table.
		static const size_t odd_prime_count = 6541;		// # odd primes with p < 2^16.

		bool sieve[sieve_size];
		uint32_t prm[odd_prime_count];
		uint32_t prm_ptr[odd_prime_count];

		prm[0] = 3; prm[1] = 5; prm[2] = 7;
		uint32_t i = 3;
		for (uint32_t k = 11; k < sp_max; k += 2)
		{
			const uint32_t s = uint32_t(std::sqrt(double(k))) + 1;
			uint32_t d; for (d = 3; d <= s; d += 2) if (k % d == 0) break;
			if (d > s) prm[i++] = k;
		}

		// if (i != odd_prime_count) throw;

		for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

		const uint64_t p0 = ((1000000000000ull * _p_min) / sp_max) * sp_max;
		const uint64_t p1 = (_p_max < 18446745) ? ((1000000000000ull * _p_max) / sp_max + 1) * sp_max : uint64_t(-1);
		std::cout << "p in [" << p0 << "; " << p1 << "] " << std::endl;

		if (_p_min == 0)
		{
			sieve[0] = true;	// p = 1
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				bool first = true;
				size_t k = (p - 1) / 2;
				for (; k < sieve_size; k += p) if (first) first = false; else sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}
		else
		{
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				size_t o = p - size_t(p0 % p); if (o % 2 == 0) o += p;
				size_t k = (o - 1) / 2;
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}

		PArray p_array;
		PArrayFiller filler(p_array);
		size_t queue_size = 0;

		for (uint64_t jp = p0; true; jp += sp_max)
		{
			for (size_t kp = 0; kp < sieve_size; ++kp)
			{
				if (!sieve[kp])
				{
					const uint64_t p = jp + 2 * kp + 1;
					if (filler.add(p))
					{
						std::lock_guard<std::mutex> guard(_p_queue_mutex);
						_p_queue.push(p_array);
						queue_size = _p_queue.size();
						if (p >= p1)
						{
							while (!filler.add(0));
							_p_queue.push(p_array);
							return;
						}
					}
				}
			}

			for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				size_t k = prm_ptr[i], p = prm[i];
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}

			while (queue_size > max_queue_size)
			{
				// std::cout << "prime_gen: waiting... p ~ " << jp + 1 << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				queue_size = _p_queue.size();
			}
		}
	}

public:
	Wieferich(const uint32_t p_min, const uint32_t p_max) : _p_min(p_min), _p_max(p_max)
	{
		std::thread t_gen_p([=] { prime_gen(); }); t_gen_p.detach();

		PArray p_array;

		int64_t A_min = uint64_t(-1) / 2;
		auto t0 = std::chrono::steady_clock::now();
		uint64_t p0 = 0;

		while (true)
		{
			bool found = false;
			{
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				if (!_p_queue.empty())
				{
					found = true;
					p_array = _p_queue.front();
					_p_queue.pop();
				}
			}

			if (!found)
			{
				// std::cout << "Waiting input..." << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(10));
			}
			else
			{
				for (size_t i = 0; i < p_size; ++i)
				{
					vec4_uint64_t p; p_array.get(i, p);
					// TODO: two_pow_mod2 on vec4_uint64_t
					for (size_t j = 0; j < 4; ++j)
					{
						const uint64_t pj = p[j];
						if (pj == 0) return;
						const M2p r = two_pow_mod2(pj - 1, pj);
						if (r.l == 1)
						{
							const int64_t a = (r.h > pj / 2) ? r.h - pj : r.h, A = std::abs(a);
							if (A <= A_min)
							{
								const char sign = (A == a) ? '+' : '-';
								std::cout << pj << ": 1 " << sign << " " << A << " p" << "                 " << std::endl;
								A_min = std::max(A, int64_t(10));
							}
						}
					}
				}

				vec4_uint64_t p; p_array.get(p_size - 1, p);
				const uint64_t p1 = p[3];

				const auto t1 = std::chrono::steady_clock::now();
				const std::chrono::duration<double> dt = t1 - t0;
				if (dt.count() > 5)
				{
					if (p0 != 0)
					{
						const double delta_p_sec = (p1 - p0) / dt.count();
						const double sec_T = 1e12 / delta_p_sec;
						std::cout << p1 << ", " << int(sec_T) << " sec/T\r";
					}
					t0 = t1; p0 = p1;
				}
			}
		}
	}

	virtual ~Wieferich() {}
};

int main(int argc, char * argv[])
{
	std::cerr << "wieferich: search for Wieferich primes" << std::endl;
	std::cerr << " Copyright (c) 2020, Yves Gallot" << std::endl;
	std::cerr << " wieferich is free source code, under the MIT license." << std::endl << std::endl;
	std::cerr << " Usage: wieferich <p_min> <p_max>" << std::endl;
	std::cerr << "   p_min: the start of the p range, in T (10^12) values (default 0)" << std::endl;
	std::cerr << "   p_max: the end of the p range, in T (10^12) values (default p_min + 1)" << std::endl;

	const uint32_t p_min = (argc > 1) ? std::min(std::atoi(argv[1]), 18446744) : 0;
	const uint32_t p_max = (argc > 2) ? std::min(std::atoi(argv[2]), 18446745) : p_min + 1;

	Wieferich(p_min, p_max);

	return EXIT_SUCCESS;
}
