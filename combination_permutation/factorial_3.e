note
	description: "Summary description for {FACTORIAL}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	FACTORIAL_3

feature
	factorial_loop (n: INTEGER): INTEGER_64
		note
			explicit: contracts
		require
			input_in_range: n >= 0 and n <= 20
		local
			count: INTEGER
		do
			from
				Result := 1
				count := 1
			invariant
				count_not_big: count >= 1 and count <= n + 1
				result_is_positive: Result > 0
				correct_until_now: Result = factorial_rec (count - 1)
			until
				count > n
			loop
				Result := Result * count
				count := count + 1
			variant
				n - count + 1
			end
		ensure
			result_is_positive: Result >= 1
			result_is_correct: Result = factorial_rec (n)
		end

	factorial_rec (n: INTEGER): INTEGER_64
		note
			explicit: contracts
		require
			input_in_range: n >= 0 and n <= 20
		do
			if
				n = 0
			then
				Result := 1
			else
				Result := factorial_rec (n - 1) * n
			end
		ensure
			result_is_positive: Result >= 0
			if_zero: n = 0 implies Result = 1
			if_not_zero: n /= 0 implies Result = factorial_rec (n - 1) * n
		end

end
