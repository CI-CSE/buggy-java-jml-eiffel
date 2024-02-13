note
	description: "Summary description for {COMBINATION_PERMUTATION}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	COMBINATION_PERMUTATION_3
feature {NONE}
	fac: FACTORIAL_3
		do
			create Result
		end
feature {NONE}
	combination (n: INTEGER; r: INTEGER): INTEGER_64
		require
			input_in_range: 0 <= n and n <= 20 and 0 <= r and r <= n
			fac_is_correct: fac /= Void
		do
			Result := fac.factorial_loop (n) * (fac.factorial_loop (r) * fac.factorial_loop (n - r))
--			Result := fac.factorial_loop (n) // (fac.factorial_loop (r) * fac.factorial_loop (n - r))
		ensure
			result_is_correct: Result = fac.factorial_rec (n) // (fac.factorial_rec (r) * fac.factorial_rec (n - r))
		end

	permutation (n: INTEGER; r: INTEGER): INTEGER_64
		require
			input_in_range: 0 <= n and n <= 20 and 0 <= r and r <= n
		do
			Result := fac.factorial_loop (n) // fac.factorial_loop (n - r)
		ensure
			result_is_correct: Result = fac.factorial_rec (n) // fac.factorial_rec (n - r)
		end

	select_either (n: INTEGER; r: INTEGER; flag: BOOLEAN): INTEGER_64
		require
			input_in_range: 0 <= n and n <= 20 and 0 <= r and r <= n
		do
			if flag then
				Result := combination (n, r)
			else
				Result := permutation (n, r)
			end
		ensure
			if_flag: flag implies Result = fac.factorial_rec (n) // (fac.factorial_rec (r) * fac.factorial_rec (n - r))
			else_flag: not flag implies Result = fac.factorial_rec (n) // fac.factorial_rec (n - r)
		end
end
