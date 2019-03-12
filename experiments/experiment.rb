
# ROOT = `pwd`.chomp
# cat in.csv | cut -d, -f1
# sed 's/\([^,]*\),\(.*\)/\2/'  Input_file
# awk '{sub(/[^,]*/,"");sub(/,/,"")} 1'   Input_file

puts "running"
ϵs = [0.0001, 0.001, 0.01, 0.1]
run = "examples/gd-pb-mini.ed.duet"
xs = "data_short/ffxs.csv"
ys = "data_short/ffys.csv"
def accuracy(ϵ,run,xs,ys)
  is = 1000
  r = 1
  s = 50
  η = `wc -l #{ys}`.to_i
  δ = 1.0/(η*η)
  puts `stack run -- run #{run} #{xs} #{ys} #{ϵ} #{is} #{δ} #{δ} #{r} #{s}`
  puts `stack run -- lr-accuracy #{xs} #{ys} out/model.csv`
  accl = File.read "out/acc.csv"
  al = accl.split(",").map(&:to_f)
  acc = al[0]/(al[0]+al[1])
  # puts acc
end
as = ϵs.map { |ϵ| accuracy(ϵ,run,xs,ys) }

puts as

puts "done"
