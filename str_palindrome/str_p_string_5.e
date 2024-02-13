note
	model: sequence

class
	STR_P_STRING_5

create
	make_empty, make_from_sequence

feature

	make_empty
		do
			create sequence
		ensure
			sequence.is_empty
		end

	make_from_sequence (s: MML_SEQUENCE [CHARACTER])
		do
			sequence := s
		ensure
			sequence ~ s
		end

	char_extended (c: CHARACTER): STR_P_STRING_5
		note
			status: impure
		local
			seq: MML_SEQUENCE [CHARACTER]
		do
			create seq.singleton (c)
			seq := sequence + seq
			create Result.make_from_sequence (seq)
		ensure
			Result.sequence [Result.sequence.count] = c
			Result.sequence = sequence.extended (c)
			Result.count = count + 1

			Result.is_wrapped
			Result.is_fresh
		end

	count: INTEGER
		note
			status: functional
		do
			Result := sequence.count
		end

	item alias "[]" (i: INTEGER): CHARACTER
		require
			index_in_bounds: 1 <= i and i <= count
		do
			Result := sequence [i]
		ensure
			Result = sequence [i]
		end

feature
	sequence: MML_SEQUENCE [CHARACTER]

end
