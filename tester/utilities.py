def modulepath(name, *path):
    import sys
    import os.path
    return os.path.join(os.path.realpath(os.path.dirname(sys.modules[name].__file__)), *path)

def load_source(name, module_name):
    import imp
    return imp.load_source(module_name, modulepath(__name__, module_name))

mean = lambda xs: sum(xs) / len(xs)

def bind_maybe(mx, fxmy):
    if mx is None:
        return None
    else:
        return fxmy(mx)

def uncurry(f):
    return lambda xs: f(xs[0], xs[1])

def map_maybe(f, xs):
    return [y for y in [f(x) for x in xs] if y is not None]

# Like dict.get, but for lists
def list_get(xs, i, default):
    if i < len(xs):
        return xs[i]
    else:
        return default

def format_latex_table(rows):
    col_width = {}
    for row in rows:
        for col_i, cell in enumerate(row):
            col_width[col_i] = max(col_width.get(col_i, 0), len(cell))
    
    rows = [[cell.ljust(col_width[col_i]) for col_i, cell in enumerate(row)] for row in rows]
    
    return "\n".join([" & ".join(row) + " \\\\" for row in rows])    

def format_csv(rows):
    return "\n".join([",".join(row) for row in rows])

def show_round(x, dp):
    # There is probably a better way to do this, but I'm on a train and can't look it up
    s = str(round(x, dp))
    if '.' in s:
        before, after = s.split('.')
        return before + '.' + after + ('0' * (dp - len(after)))
    else:
        return s + '.' + ('0' * dp)

def show_percentage_difference(x):
    return str(int(round((x - 1) * 100, 0))) + "%"

def assert_eq(left, right):
    assert left == right, repr(left) + " != " + repr(right)

def zipwith_dict(f, left, right):
    thekeys = left.keys()
    assert_eq(thekeys, right.keys())
    
    return dict([(key, f(key, left[key], right[key])) for key in thekeys])

def union_dict(left, right):
    new = dict(left)
    new.update(right)
    return new

def restrict_dict(what, to):
    new = {}
    for key in to:
      new[key] = what[key]
    
    return new

def map_dict(f, xs):
    return dict([f(k, v) for k, v in xs.items()])

def map_maybe_dict(f, xs):
    return dict(map_maybe(uncurry(f), xs.items()))

def map_dict_values(f, xs):
    return dict([(k, f(k, v)) for k, v in xs.items()])

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
            headers, valuess = (strip_all(lines[0].split("&")), [strip_all(line.split("&")) for line in lines[1:]])
            
            key_header = headers.pop(0)
            
            def makeresult(values):
                filename = values.pop(0)
                return (filename, dict(zip(headers, values)))
            self.results = dict([makeresult(values) for values in valuess])
            
            self.key_header = key_header
            self.headers = headers
        elif len(args) == 4:
            description, key_header, headers, results = args[0], args[1], args[2], args[3]
            
            self.description = description
            self.key_header = key_header
            self.headers = headers
            self.results = results
        else:
            assert False

    @classmethod
    def zipresults(cls, zip_descriptions, zip_values, left, right):
        combine_files = lambda _filename, left_values, right_values: zipwith_dict(zip_values, left_values, right_values)
        combine_results = lambda leftresults, rightresults: zipwith_dict(combine_files, leftresults, rightresults)
        return cls.combineresults(zip_descriptions, combine_results, left, right)
    
    @classmethod
    def combineresults(cls, combine_descriptions, combine_results, left, right):
        assert_eq(left.key_header, right.key_header)
        
        common_headers = set(left.headers).intersection(set(right.headers))
        if common_headers != set(left.headers):
            discarded = set(left.headers).symmetric_difference(set(right.headers))
            import sys
            print >> sys.stderr, "Warning: discarding mismatched data for " + ", ".join(discarded)
        
        restrict = lambda results: map_dict_values(lambda filename_, columns: restrict_dict(columns, common_headers), results)
        return Results(combine_descriptions(left.description, right.description), left.key_header, left.headers, combine_results(restrict(left.results), restrict(right.results)))
    
    def __str__(self):
        return self.latex()
    
    def latex(self):
        return "\n".join([self.description, format_latex_table(self.table())])
    
    def csv(self):
        return format_csv(self.table())
    
    def table(self):
        comparing = lambda f: lambda x, y, f=f: cmp(f(x), f(y))
        # NB: the point of this isupper() stuff is so that the "filenames" beginning with capital letters are sorted at the end.
        # I do this because in fact only the summary "filenames" (like Average and Maximum) begin with capital letters.
        return [[self.key_header] + self.headers] + [[filename] + [values[header] for header in self.headers] for filename, values in sorted(self.results.items(), comparing(lambda x: (x[0][0].isupper(), x[0])))]
    
    def columns(self):
        columns = {}
        for filename, everything in self.results.items():
            columns[self.key_header] = columns.get(self.key_header, []) + [filename]
            for header, value in everything.items():
                columns[header] = columns.get(header, []) + [value]
        
        return columns
