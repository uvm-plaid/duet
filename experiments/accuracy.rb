
# cat in.csv | cut -d, -f1
# sed 's/\([^,]*\),\(.*\)/\2/'  Input_file

puts "running"
SAMPLE = 10 # ← limited testing, 50
LR = 1
ITERS = 1000
ϵs = [0.0001, 0.001, 0.01, 0.1, 1, 10, 100][0..1] # ← limited testing
run = "examples/gd-pb-mini.ed.duet"
xs = "data_short/ffxs.csv"
ys = "data_short/ffys.csv"
def accuracy(ϵ,run,xs,ys)
  η = `wc -l #{ys}`.to_i
  δ = 1.0/(η*η)
  puts `stack run -- run #{run} #{xs} #{ys} #{ϵ} #{ITERS} #{δ} #{δ} #{LR} #{SAMPLE}`
  puts `stack run -- lr-accuracy #{xs} #{ys} out/model.csv`
  accl = File.read "out/acc.csv"
  al = accl.split(",").map(&:to_f)
  acc = al[0]/(al[0]+al[1])
end
as = ϵs.map { |ϵ| accuracy(ϵ,run,xs,ys) }

puts as

puts "done"
