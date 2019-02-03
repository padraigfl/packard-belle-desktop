import React, { Component } from "react";
import { Rnd } from "react-rnd";
import { WindowExplorer } from "packard-belle";
import "./_styles.scss";

class Explorer extends Component {
  state = {
    width: this.props.initialWidth || this.props.minWidth,
    height: this.props.initialHeight || this.props.minHeight,
    x: 0,
    y: 0,
    maximized: false
  };

  updateLocation = (a, b) => this.setState({ x: b.x, y: b.y });
  resize = (e, direction, ref, delta, position) =>
    this.setState({
      width: ref.style.width,
      height: ref.style.height,
      ...position
    });
  maximize = () => this.setState({ maximized: true });
  restore = () => this.setState({ maximized: false });

  render() {
    return (
      <Rnd
        size={{ width: this.state.width, height: this.state.height }}
        position={{ x: this.state.x, y: this.state.y }}
        onDragStop={this.updateLocation}
        onResize={this.resize}
        scale={2}
        dragHandleClassName="Window__title"
        resizeHandleClasses={{ bottomRight: "potato" }}
        bounds=".w98"
        minWidth={this.props.initialWidth}
        minHeight={this.props.initialHeight}
        maxWidth={this.props.maxWidth}
        maxHeight={this.props.maxHeight}
      >
        <WindowExplorer
          title="Needs default"
          footer={[
            { text: "needs 100% width height" },
            { text: "overflow control" }
          ]}
          onClose={() => {
            /* needs default visibles */
          }}
          onRestore={this.restore}
          onMaximize={this.maximize}
        />
      </Rnd>
    );
  }
}

Explorer.defaultProps = {
  minWidth: 160,
  minHeight: 160,
  maxWidth: 635,
  maxHeight: 448,

  scale: 1,
  title: "Needs default"
};

export default Explorer;
