import React from "react";
import { Rnd } from "react-rnd";
import { ScaleContext } from "../../contexts/scale";

class Window extends React.PureComponent {
  static contextType = ScaleContext;
  state = {
    width: this.props.initialWidth || this.props.minWidth,
    height: this.props.initialHeight || this.props.minHeight,
    x: 0,
    y: 0,
    maximized: false,
    changingState: false
  };

  updateLocation = (a, b) =>
    this.setState({ x: b.x, y: b.y, changingState: false });
  resize = (e, direction, ref, delta, position) =>
    this.setState({
      width: ref.style.width,
      height: ref.style.height,
      ...position
    });
  maximize = () => this.setState({ maximized: true });
  restore = () => this.setState({ maximized: false });
  toggleChanging = val => () => this.setState({ changingState: val });

  render() {
    return (
      <ScaleContext.Consumer>
        {context => (
          <Rnd
            size={
              !this.state.maximized
                ? { width: this.state.width, height: this.state.height }
                : { width: "101%", height: "101%" }
            }
            position={
              !this.state.maximized
                ? { x: this.state.x, y: this.state.y }
                : { x: -2, y: -3 }
            }
            dragHandleClassName="Window__title"
            onDragStart={this.toggleChanging(true)}
            onDragStop={!this.state.maximized && this.updateLocation}
            disableDragging={this.state.maximized}
            enableResizing={
              this.state.maximized
                ? false
                : {
                    bottom: true,
                    bottomLeft: true,
                    bottomRight: true,
                    left: true,
                    right: true,
                    top: true,
                    topLeft: true,
                    topRight: false
                  }
            }
            onResize={!this.state.maximized && this.resize}
            onResizeStart={this.toggleChanging(true)}
            onResizeStop={this.toggleChanging(false)}
            bounds=".w98"
            minWidth={this.props.minWidth}
            minHeight={this.props.minHeight}
            maxWidth={this.props.maxWidth}
            maxHeight={this.props.maxHeight}
            scale={context.scale}
            onMouseDown={
              this.props.moveToTop
                ? () => this.props.moveToTop(this.props)
                : undefined
            }
          >
            {this.props.children(this)}
          </Rnd>
        )}
      </ScaleContext.Consumer>
    );
  }
}

Window.defaultProps = {
  minWidth: 160,
  minHeight: 160,
  maxWidth: 635,
  maxHeight: 448,

  scale: 1,
  title: "Needs default"
};

export default Window;
