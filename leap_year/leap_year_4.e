class
	LEAP_YEAR_4

feature
	is_leap_year (year: INTEGER): BOOLEAN
		require
			year_non_neg: 0 < year
		do
			Result := False

			if year \\ 4 = 0 then
				if year \\ 100 /= 0 then -- if year \\ 100 = 0 then
					if year \\ 400 = 0 then
						Result := True
					else
						Result := False
					end
				else
					Result := True
				end
			else
				Result := False
			end
		ensure
			when_no_4: year \\ 4 /= 0 ⇒ Result = False
			when_4_no_100: year \\ 4 = 0 and year \\ 100 /= 0 ⇒ Result = True
			when_4_100_no_400: year \\ 4 = 0 and year \\ 100 = 0 and year \\ 400 /= 0 ⇒ Result = False
			when_4_100_400: year \\ 4 = 0 and year \\ 100 = 0 and year \\ 400 = 0 ⇒ Result = True
		end

end
