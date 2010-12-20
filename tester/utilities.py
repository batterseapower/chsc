def format_latex_table(rows):
    if True:
        col_width = {}
        for row in rows:
            for col_i, cell in enumerate(row):
                col_width[col_i] = max(col_width.get(col_i, 0), len(cell))
        
        rows = [[cell.ljust(col_width[col_i]) for col_i, cell in enumerate(row)] for row in rows]
    
    return "\n".join([" & ".join(row) + " \\\\" for row in rows])

def zipwith_dict(f, left, right):
    thekeys = left.keys()
    assert(thekeys == right.keys())
    
    return dict([(key, f(key, left[key], right[key])) for key in thekeys])

def union_dict(left, right):
    new = dict(left)
    new.update(right)
    return new

def readfile(filename):
    if filename == "-":
        import sys
        result = sys.stdin.read()
    else:
        f = open(filename, 'r')
        result = f.read()
        f.close()
    
    return result


class Results(object):
    def __init__(self, *args):
        if len(args) == 1:
            contents = args[0]
            
            lines = contents.split("\n")
    
            self.description, lines = lines[0], [line.rstrip(" \\\\") for line in lines[1:] if line.strip() != ""]
    
            strip_all = lambda xs: [x.strip() for x in xs]
            headers, valuess = (strip_all(lines[0].split(" & ")), [strip_all(line.split(" & ")) for line in lines[1:]])
            
            def makeresult(values):
                everything = dict(zip(headers, values))
                filename = everything.pop("Filename")
                return (filename, everything)
            self.results = dict([makeresult(values) for values in valuess])
            
            del headers[headers.index("Filename")]
            self.headers = headers
        elif len(args) == 3:
            description, headers, results = args[0], args[1], args[2]
            
            self.description = description
            self.headers = headers
            self.results = results
        else:
            assert False

    @classmethod
    def zipresults(cls, zip_descriptions, zip_values, left, right):
        theheaders = left.headers
        assert theheaders == right.headers
        
        combine_files = lambda _filename, left_values, right_values: zipwith_dict(zip_values, left_values, right_values)
        return Results(zip_descriptions(left.description, right.description), left.headers, zipwith_dict(combine_files, left.results, right.results))
    
    def __str__(self):
        comparing = lambda f: lambda x, y, f=f: cmp(f(x), f(y))
        # NB: the point of this isupper() stuff is so that the "filenames" beginning with capital letters are sorted at the end.
        # I do this because in fact only the summary "filenames" (like Average and Maximum) begin with capital letters.
        table = [["Filename"] + self.headers] + [[filename] + [values[header] for header in self.headers] for filename, values in sorted(self.results.items(), comparing(lambda x: (x[0][0].isupper(), x[0])))]
        return "\n".join([self.description, format_latex_table(table)])
    
    def columns(self):
        columns = {}
        for filename, everything in self.results.items():
            columns["Filename"] = columns.get("Filename", []) + [filename]
            for header, value in everything.items():
                columns[header] = columns.get(header, []) + [value]
        
        return columns
    
    def summarised(self):
        mean = lambda xs: sum(xs) / len(xs)
        def lift_string(f, xs):
            try:
                return str(round(f([float(x) for x in xs]), 2))
            except ValueError, e:
                return "" # Typically happens because one of the source values is unavailable
        
        columns = self.columns()
        summary_rows = [(summary, dict([(header, lift_string(summarise, columns[header])) for header in self.headers])) for summary, summarise in [("Maximum", max), ("Minimum", min), ("Average", mean)]]
        return Results(self.description, self.headers, union_dict(self.results, dict(summary_rows)))
