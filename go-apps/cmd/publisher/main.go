package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"os/exec"
	"os/user"

	"github.com/videocoin/zk-storage-proof/go-apps/sla"
)

func main() {
	usr, _ := user.Current()
	binFolder := flag.String("bin", "/usr/bin/", "folder zktrans containing binaries")
	workFolder := flag.String("work", usr.HomeDir+"/test/", "folder containing intermediate files")
	input := flag.String("input", "test", "input file")
	flag.Parse()

	fmt.Println("Args ", *input)
	cmd := exec.Command(*binFolder+"extract-frame", "-f", "0", "-c", "300", "--scale", "--input", *input, "--output", *workFolder+"scaled-frames.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err := cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("extracting frames")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	cmd = exec.Command(*binFolder+"rust-phash", *workFolder+"scaled-frames.txt", *workFolder+"phashes.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating phashes")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	// zksnarks proof
	cmd = exec.Command(*binFolder+"zkptrans", "zkporgenproof", *workFolder+"zkpor_crs.dat", *workFolder+"zkpor_proof.dat", *workFolder+"phashes.txt", *workFolder+"zkpor_witness.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating proof")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	publicInputs := sla.ZkPublicInput{
		Leaf: "0x0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF",
		Root: "0x0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF",
		Path: "0x0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF",
	}
	publicInputs_json, err := json.Marshal(publicInputs)
	// Create request
	sla := sla.SlaStorage{
		Url:          "https://test.storage.com/stream1.ts",
		ProofType:    sla.ProofPhashMerkleZksnark,
		PublicInputs: string(publicInputs_json),
	}
	sla_json, err := json.Marshal(sla)

	hasher := sha256.New()
	hasher.Write(sla_json)
	sla_id := base64.URLEncoding.EncodeToString(hasher.Sum(nil))
	reward := "1vid"
	cmd = exec.Command("vccli", "tx", "sla", "createSla", reward, sla_id, string(sla_json), "--yes", "--from", "tester0")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating transaction")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	fmt.Println("Finished:", err)
}

func print(console io.ReadCloser) {
	scanner := bufio.NewScanner(console)
	scanner.Split(bufio.ScanWords)
	for scanner.Scan() {
		m := scanner.Text()
		fmt.Print(m + " ")
	}
}
