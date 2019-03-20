
module Enumerable
  def sum
    self.inject(0){|accum, i| accum + i }
  end

  def mean
    self.sum/self.length.to_f
  end

  def variance
    m = self.mean
    sum = self.inject(0){|accum, i| accum +(i-m)**2 }
    sum/(self.length - 1).to_f
  end

  def std_dev
    Math.sqrt(self.variance)
  end
end

# cat in.csv | cut -d, -f1
# sed 's/\([^,]*\),\(.*\)/\2/'  Input_file

puts "running"
RUNS = 5
SAMPLE = 10 # ← limited testing, 50
LR = 1
ITERS = 100 # ← limited testing, 1000
ϵs = [0.001, 0.01, 0.1, 1, 10][0..1] # ← limited testing
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

runs = []
ams = []
asds = []
trials = ϵs.length
RUNS.times do |i|
  runs << ϵs.map { |ϵ| accuracy(ϵ,run,xs,ys) }
end
trials.times do |i|
  ams << runs.map { |l| l[i] }.mean
  asds << runs.map { |l| l[i] }.std_dev
end

puts "MEANs: #{ams}"
puts "STDDEVs: #{asds}"

puts "done"
